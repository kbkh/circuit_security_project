// dummy
/*************************************************************************//**
                                                                            *****************************************************************************
                                                                            * @file        sat.cpp
                                                                            * @brief
                                                                            * @author      Frank Imeson
                                                                            * @date
                                                                            *****************************************************************************
                                                                            ****************************************************************************/

// http://www.ros.org/wiki/CppStyleGuide

#include <cstdlib>
#include <iostream>
#include <fstream>
#include "security.hpp"
#include "main.hpp"

#define DEBUG
//#define PRINT_SOLUTION
//#define MEASURE_TIME
//#define MEASURE_TIME_S1
#define USE_SOLNS
//#define NRAND
//#define VF2

//using namespace formula;
using namespace std;

// Added by Karl
// PAG
//set<long> test;
/*int maxPAGsize = 0;
vector<set<int> > edge_neighbors;
vector<PAG> pags;
map<int,vector<int> > colors;
int H_v_dummy = 0;
int H_e_dummy = 0;
int G_v_lifted = 0;
int G_e_lifted = 0;
bool start = false;
vector<set<int> > vertex_neighbors_out;
vector<set<int> > vertex_neighbors_in;
set<int> top_tier_vertices;
map<int, set<int> >top_tier_edges;*/
////////////////



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
string report (string prefix, Circuit *G, Circuit *H, int L1, int L0, Edge edge) {
    
    stringstream out;
    out << prefix
    << ": |V(G)| = " << (int) igraph_vcount(G)
    << ", |E(G)| = " << (int) igraph_ecount(G)
    << ", |V(H)| = " << (int) igraph_vcount(H)
    << ", |E(H)| = " << (int) igraph_ecount(H);
    if (L0 > 0) out << ", #L0 = " << L0;
    /*if (L1 > 0)*/ out << ", L1 = "  << L1; // Removed by Karl
    if (edge.first >= 0) out << ", +<" << edge.first << "," << edge.second << ">";
    out << endl;
    
    return out.str();
}

/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
Security::Security (Circuit *_G, Circuit *_H, Circuit *_F, Circuit *_R)
{
    G = _G;
    H = _H;
    F = _F;
    R = _R;
    
    /*igraph_vector_int_init(&colour_G, igraph_vcount(G));
    igraph_vector_int_init(&colour_H, igraph_vcount(H));
    
    for (unsigned int i=0; i<igraph_vcount(G); i++)
        VECTOR(colour_G)[i] = (int) VAN(G, "colour", i);
    
    for (unsigned int i=0; i<igraph_vcount(H); i++)
        VECTOR(colour_H)[i] = (int) VAN(H, "colour", i);*/
    
    //isosat = new Isosat(G, H, &colour_G, &colour_H, 0, 0, &igraph_compare_transitives, 0, 0);
}

Security::~Security() {
    edge_neighbors.clear();
    vector<set<int> >().swap(edge_neighbors);
    
    vertex_neighbors_in.clear();
    vector<set<int> >().swap(vertex_neighbors_in);
    
    vertex_neighbors_out.clear();
    vector<set<int> >().swap(vertex_neighbors_out);
    
    top_tier_vertices.clear();
    set<int>().swap(top_tier_vertices); //
    
    top_tier_edges.clear();
    map<int, set<int> >().swap(top_tier_edges); //
    
    pags.clear();
    vector<PAG>().swap(pags);
    
    colors.clear();
    map<int,vector<int> >().swap(colors); //
}

// Added by Karl--
void Security::get_edge_neighbors() {
    for (int i = 0; i < igraph_ecount(G); i++) {
        set<int> temp;
        edge_neighbors.push_back(temp);
        // Get vertices the edge is connected to
        int from, to;
        igraph_edge(G,i,&from,&to);
        
        // get neighbor vertices of the first vertex
        igraph_vector_t nvids;
        igraph_vector_init(&nvids, 0);
        igraph_neighbors(G, &nvids, from, IGRAPH_ALL);
        
        for (int j = 0; j < igraph_vector_size(&nvids); j++) {
            if (VECTOR(nvids)[j] != to) {
                // get id of edge connecting the 2 vertices as it's a neighbor to the target edge
                int eid;
                int nto = VECTOR(nvids)[j];
                igraph_get_eid(G, &eid, from, nto, IGRAPH_UNDIRECTED, 1);
                
                // Add the id of that edge to the set of neighbors of the target edge
                set<int>::const_iterator got = edge_neighbors[i].find(eid);
                if (got == edge_neighbors[i].end() && eid != i) // not in set + security check
                    edge_neighbors[i].insert(eid);
            }
        }
        
        // get neighbor vertices of the first vertex
        igraph_vector_destroy(&nvids);
        igraph_vector_init(&nvids, 0);
        igraph_neighbors(G, &nvids, to, IGRAPH_ALL);
        
        for (int j = 0; j < igraph_vector_size(&nvids); j++) {
            if (VECTOR(nvids)[j] != from) {
                // get id of edge connecting the 2 vertices as it's a neighbor to the target edge
                int eid;
                int nfrom = VECTOR(nvids)[j];
                igraph_get_eid(G, &eid, nfrom, to, IGRAPH_UNDIRECTED, 1);
                
                // Add the id of that edge to the set of neighbors of the target edge
                set<int>::const_iterator got = edge_neighbors[i].find(eid);
                if (got == edge_neighbors[i].end() && eid != i) // not in set + security check
                    edge_neighbors[i].insert(eid);
            }
        }
        igraph_vector_destroy(&nvids); // new addition
    }
}

void Security::create_graph(igraph_t* g, set<int> edges, set<int>& vertices_set, int* max_degree, bool create/*, map<int,int>& map12, bool mapping*/) {
    map<int,int> vertices;
    
    if (create)
        igraph_empty(g,0,IGRAPH_DIRECTED);
    
    set<int>::iterator it;
    for (it = edges.begin(); it != edges.end(); it++) {
        int from, to;
        int new_from, new_to;
        int F_from, F_to;
        
        igraph_edge(G,*it,&from,&to);
        
        // if adding vertices and egdes to H, "delete" them from G
        if (!create) {
            SETVAN(G, "Removed", from, Removed);
            SETVAN(G, "Removed", to, Removed);
            SETEAN(G, "Removed", *it, Removed);
        }
        
        map<int,int>::iterator got = vertices.find(from);
        if (got == vertices.end()) { // not in set
            igraph_add_vertices(g, 1, 0);
            
            int vid = igraph_vcount(g) - 1;
            
            if (start /*&& !mapping*/ && !create) {
                H_v_dummy++;
                igraph_add_vertices(F, 1, 0);
                SETVAN(F, "Dummy", igraph_vcount(F)-1, kDummy);
                SETVAN(F, "colour", igraph_vcount(F)-1, VAN(G, "colour", from));
                SETVAN(F, "ID", igraph_vcount(F)-1, igraph_vcount(F)-1);
                SETVAS(F, "Tier", igraph_vcount(F)-1, "Bottom");
                F_from = igraph_vcount(F)-1;
            } else if (/*!mapping &&*/!create) {
                SETVAS(F, "Tier", VAN(G, "ID", from), "Bottom");
                SETVAS(R, "Tier", VAN(G, "ID", from), "Bottom");
                F_from = VAN(G, "ID", from);
            }
            
            SETVAN(g, "colour", vid, VAN(G, "colour", from));
            SETVAN(g, "ID", vid, VAN(G, "ID", from));
            
            vertices.insert(pair<int,int>(from,vid));
            new_from = vid;
            
            // add to vertices set
            set<int>::iterator has = vertices_set.find(from);
            if (has == vertices_set.end()) // not in set, security check
                vertices_set.insert(from);
            
            if (igraph_vertex_degree(G, from) > *max_degree)
                *max_degree = igraph_vertex_degree(G, from);
            
            // "mapping" of the vertices of the new pag to vertices in G
            /*if (mapping)
                map12.insert(pair<int,int>(vid,from));
            
            // "mapping" of the vertices of H to vertices in G
            if (!create) {
                map<int,int>::iterator in = map12.find(VAN(G,"ID",from));
                
                if (in == map12.end()) // not in set
                    map12.insert(pair<int,int>(VAN(G,"ID",from),vid));
            }*/
        } else new_from = vertices[from];
        
        got = vertices.find(to);
        if (got == vertices.end()) { // not in set
            igraph_add_vertices(g, 1, 0);
            
            int vid = igraph_vcount(g) - 1;
            
            if (start /*&& !mapping*/ && !create) {
                H_v_dummy++;
                igraph_add_vertices(F, 1, 0);
                SETVAN(F, "Dummy", igraph_vcount(F)-1, kDummy);
                SETVAN(F, "colour", igraph_vcount(F)-1, VAN(G, "colour", to));
                SETVAN(F, "ID", igraph_vcount(F)-1, igraph_vcount(F)-1);
                SETVAS(F, "Tier", igraph_vcount(F)-1, "Bottom");
                F_to = igraph_vcount(F)-1;
            } else if (/*!mapping &&*/ !create) {
                SETVAS(F, "Tier", VAN(G, "ID", to), "Bottom");
                SETVAS(R, "Tier", VAN(G, "ID", to), "Bottom");
                F_to = VAN(G, "ID", to);
            }
            
            SETVAN(g, "colour", vid, VAN(G, "colour", to));
            SETVAN(g, "ID", vid, VAN(G, "ID", to));
            vertices.insert(pair<int,int>(to,vid));
            new_to = vid;
            
            // add to vertices set
            set<int>::iterator has = vertices_set.find(to);
            if (has == vertices_set.end()) // not in set, security check
                vertices_set.insert(to);
            
            if (igraph_vertex_degree(G, to) > *max_degree)
                *max_degree = igraph_vertex_degree(G, to);
            
            /*if (mapping)
                map12.insert(pair<int,int>(vid,to));
            
            if (!create) {
                map<int,int>::iterator in = map12.find(VAN(G,"ID",to));
                
                if (in == map12.end()) // not in set
                    map12.insert(pair<int,int>(VAN(G,"ID",to),vid));
            }*/
        } else new_to = vertices[to];
        
        igraph_add_edge(g, new_from, new_to);
        
        if (start /*&& !mapping*/ && !create) {
            H_e_dummy++;
            igraph_add_edge(F, F_from, F_to);
            SETEAN(F, "Dummy", igraph_ecount(F)-1, kDummy);
//            SETEAN(F, "colour", igraph_ecount(F)-1, EAN(G, "colour", to));
            SETEAS(F, "Tier", igraph_ecount(F)-1, "Bottom");
        } else if (/*!mapping && */!create) {
            SETEAS(F, "Tier", EAN(G, "ID", *it), "Bottom");
            SETEAS(R, "Tier", EAN(G, "ID", *it), "Bottom");
        }
        
        SETEAN(g, "ID", igraph_ecount(g)-1, EAN(G, "ID", *it));
    }
}

void Security::isomorphic_test(set<int> current_subgraph) {
    //map<int,int> mapPAGG; // mapping of the new pag from its vertices to G
    set<int> vert;
    igraph_t new_pag; // deleted this
    int max_degree = 0;
    
    create_graph(&new_pag, current_subgraph, vert, &max_degree);
    
    
    igraph_vector_t color11; // deleted this
    igraph_vector_init(&color11, 0);
    igraph_vector_int_t color1; // deleted this
    igraph_vector_int_init(&color1, 0);
    
    VANV(&new_pag, "colour", (igraph_vector_t*) &color11);
    for (int i = 0; i < igraph_vector_size(&color11); i++)
        igraph_vector_int_push_back(&color1, VECTOR(color11)[i]);
    
    //            // debug
    //            for (int i = 0; i < igraph_vcount(&new_pag); i++) {
    //                if (i == 0)
    //                    cout<<"new_pag:"<<endl;
    //                cout<<"     ID: "<<VAN(&new_pag, "ID", i)<<" "<<VAN(&new_pag, "colour", i)<<endl;
    //            }
    //            //--
    
    // Check if this subgraph alrady has an isomorphic pag. If it does, it's an embedding of that pag
    igraph_bool_t iso = false;
    // debug
    int index = 0;
    //--
    
   // igraph_vector_t* map12 = new igraph_vector_t; // pointer
   // igraph_vector_init(map12, 0);
    
    for (int i = 0; i < pags.size(); i++) {
        // debug
        index = i;
        //--
        
        // create the subgraphs
       // map<int,int> dummy;
        set<int> dumy;
        int dum;
        igraph_t pag; // deleted this
        create_graph(&pag, pags[i].pag, dumy, &dum);
        
        if (igraph_vcount(&pag) != igraph_vcount(&new_pag))
            continue;
        
        igraph_vector_t color22; // deleted this
        igraph_vector_init(&color22, 0);
        igraph_vector_int_t color2; // deleted this
        igraph_vector_int_init(&color2, 0);
        
        VANV(&pag, "colour", (igraph_vector_t*) &color22);
        for (int j = 0; j < igraph_vector_size(&color22); j++)
            igraph_vector_int_push_back(&color2, VECTOR(color22)[j]);
        //                cout<<"1: "<<igraph_vector_size(&color11)<<" 2: "<<igraph_vector_size(&color22)<<endl;
        igraph_isomorphic_vf2(&pag, &new_pag, &color2, &color1, NULL, NULL, &iso, /*map12*/NULL, NULL, NULL, NULL, NULL);
        
        igraph_destroy(&pag); // new addition
        igraph_vector_destroy(&color22); // new addition
        igraph_vector_int_destroy(&color2); // new addition
        
        if (iso)
            break;
    }
    
    igraph_destroy(&new_pag); // new addition
    igraph_vector_destroy(&color11); // new addition
    igraph_vector_int_destroy(&color1); // new addition
    
    if (!iso) {
        //                // debug
        //                cout<<"nope: ";
        //                set<int>::iterator it;
        //                for (it = current_subgraph.begin(); it != current_subgraph.end(); it++)
        //                    cout<<*it<<" ";
        //                cout<<endl;
        //                //--
        
        // add this subgraph to the pags
        PAG temp_pag;
        pags.push_back(temp_pag);
        pags[pags.size()-1].pag = current_subgraph;
       //pags[pags.size()-1].mapPAGG = mapPAGG; // newremoved
        pags[pags.size()-1].vertices = vert;
        pags[pags.size()-1].max_degree = max_degree;
        pags[pags.size()-1].processed = false;
    } else {
        //                // debug
        //                cout<<"yup: ";
        //                set<int>::iterator it;
        //                for (it = pags[index].pag.begin(); it != pags[index].pag.end(); it++)
        //                    cout<<*it<<" ";
        //                cout<<"and ";
        //                for (it = current_subgraph.begin(); it != current_subgraph.end(); it++)
        //                    cout<<*it<<" ";
        //                cout<<endl;
        //                //--
        
        // add it to the list of embedding for that PAG
        EMBEDDINGS temp;
        pags[index].embeddings.push_back(temp);
        pags[index].embeddings[pags[index].embeddings.size()-1].edges = current_subgraph;
        
       /* for (int i = 0; i < igraph_vector_size(map12); i++)
            igraph_vector_set(map12, i, VAN(&new_pag, "ID", igraph_vector_e(map12,i))); */
        
        //pags[index].embeddings[pags[index].embeddings.size()-1].map = map12; // newremoved
        pags[index].embeddings[pags[index].embeddings.size()-1].max_degree = 0;
        pags[index].embeddings[pags[index].embeddings.size()-1].vertices = vert;
        pags[index].embeddings[pags[index].embeddings.size()-1].max_degree = max_degree;
    }
}

void Security::subgraphs(int v, set<int> current_subgraph, set<int> possible_edges, set<int> neighbors) {
    if (maxPAGsize == 1)
        isomorphic_test(current_subgraph);
    else if (current_subgraph.size() == maxPAGsize-1) {
        //        // debug
        //        cout<<"subgraphs of size "<<maxPAGsize<<":"<<endl;
        //        string first;
        //
        //        set<int>::iterator it1;
        //        for (it1 = current_subgraph.begin(); it1 != current_subgraph.end(); it1++) {
        //            stringstream ss;
        //            ss << *it1;
        //            string str = ss.str();
        //            first = first + " " + str;
        //        }
        
        set<int>::iterator it;
        //        for (it = possible_edges.begin(); it != possible_edges.end(); it++)
        //            cout<<first<<" "<<*it<<endl;
        //        //--
        
        // Every edge in the possible list will give a new subgrph so to save them they are added to the current subgraph one after the other
        for (it = possible_edges.begin(); it != possible_edges.end(); it++) {
            // add an edge to the current subgraph
            current_subgraph.insert(*it);
            
            isomorphic_test(current_subgraph);
            
            // bring back the current subgraph to how it was to add another edge from the list
            current_subgraph.erase(*it);
        }
        
        return;
    }
    
    while (!possible_edges.empty()) {
        // don't want to modify the graph for next edge to be added to form a new subgraph
        set<int> temp_subgraph = current_subgraph;
        // add the first edge in the list
        int new_edge = *possible_edges.begin();
        
        set<int>::iterator got = temp_subgraph.find(new_edge);
        if (got == temp_subgraph.end()) // not in set
            temp_subgraph.insert(new_edge);
        // remove it from the list because it can't be part of it for this graph of the next since it's a neighbor of an edge in the graph
        possible_edges.erase(possible_edges.begin());
        
        // add the rest of the list to the list of the new subgraph
        set<int> temp_edges = possible_edges;
        set<int>::iterator it;
        // for every neighbor of the newly added edge
        for (it = edge_neighbors[new_edge].begin(); it != edge_neighbors[new_edge].end(); it++) {
            int neighbor = *it;
            // check if it's bigger than the original edge of this family of subgraphs, if it's not then the subgraphs containing these 2 are already created
            if (neighbor > v) {
                set<int>::iterator got = neighbors.find(neighbor);
                // check if it's the neighbor of one of the other edges in the graph as well. If it is, the subgraphs containing these edges are already created
                if (got == neighbors.end()) // not in set
                    temp_edges.insert(neighbor);
            }
        }
        
        // the neighbors should stay the same for the next edge so a copy is created so that the updated version can be sent to the subgraphs created from these edges
        set<int> temp_neighbors = neighbors;
        temp_neighbors.insert(edge_neighbors[new_edge].begin(), edge_neighbors[new_edge].end());
        
        subgraphs(v, temp_subgraph, temp_edges, temp_neighbors);
    }
}

void Security::find_VD_embeddings(int i) {
    //cout<<"pags: "<<i<<endl;
    // add the pag itself to the embeddings to be studied because it is a part of the graph
    EMBEDDINGS temp;
    pags[i].embeddings.push_back(temp);
    pags[i].embeddings[pags[i].embeddings.size()-1].edges = pags[i].pag;
    pags[i].embeddings[pags[i].embeddings.size()-1].max_degree = pags[i].max_degree;
    pags[i].embeddings[pags[i].embeddings.size()-1].vertices = pags[i].vertices;
    
    pags[i].vd_embeddings.vd_embeddings.clear();
    pags[i].vd_embeddings.max_degree = 0;
    pags[i].vd_embeddings.max_count = 0;
    
    // Initialization
    for (int j = 0; j < pags[i].embeddings.size(); j++) {
        pags[i].embeddings[j].connected_embeddings.clear();
        pags[i].embeddings[j].size = 0;
    }
    
    map<int,set<int> > size;
    
    // for every embedding ...
    for (int j = 0; j < pags[i].embeddings.size(); j++) {
        // ... look at the other embeddings ...
        for (int k = j+1; k < pags[i].embeddings.size(); k++) {
            set<int>::iterator it;
            // ... for every vertex in the embedding studied ...
            for (it = pags[i].embeddings[j].vertices.begin(); it != pags[i].embeddings[j].vertices.end(); it++) {
                set<int>::iterator got = pags[i].embeddings[k].vertices.find(*it);
                // ... see if it is in the other embeddings of the same pag
                if (got != pags[i].embeddings[k].vertices.end()) { // in set, they are connected
                    pags[i].embeddings[j].connected_embeddings.insert(k);
                    pags[i].embeddings[k].connected_embeddings.insert(j);
                    break; // break and move to the next embeding
                }
            }
        }
        
        int temp_size = pags[i].embeddings[j].connected_embeddings.size();
        pags[i].embeddings[j].size = temp_size;
        // see if we already found an embedding with this many not vd embeddings
        // in both cases add the id of the new embedding to that
        map<int, set<int> >::iterator got = size.find(temp_size);;
        if (got == size.end()) { // not in set
            set<int> temp;
            temp.insert(j);
            size.insert(pair<int,set<int> >(temp_size, temp));
        } else size[temp_size].insert(j); // in set
    }
    
    // while there are embeddings that have connected embeddings (they are not vd embeddings) we remove from the candidate list the embedding that is conncted to the most embeddings
    // size->first is the # of connected embeddings, size->second is the ids of the embeddings that have that many conneceted embeddings
    while (size.size() > 1 || size.begin()->first != 0) {
        //            cout<<"YAS"<<endl;
        // access last element (in c++ map is sorted automatically everytime we insert an element)
        map<int,set<int> >::iterator itr = size.end();
        itr--;
        
        // get id of embedding to remove
        set<int> remove = itr->second;
        // if more than one have that much connected embeds then we take the first one
        int to_remove = *remove.begin();
        //            cout<<to_remove<<endl;
        // remove it from the set of embeds that have that much connected embeds
        itr->second.erase(to_remove);
        // to mark that it already have been considered
        pags[i].embeddings[to_remove].size = -1;
        
        // if it was the last one with that much connected embeds, update map
        if (itr->second.empty())
            size.erase(itr->first);
        
        // update size map and size for every connected embedding
        set<int>::iterator itera;
        for (itera = pags[i].embeddings[to_remove].connected_embeddings.begin(); itera != pags[i].embeddings[to_remove].connected_embeddings.end(); itera++) {
            int old_size = pags[i].embeddings[*itera].size;
            // if it was considered, skip, we don't want to put it back in the size map
            if (old_size == -1)
                continue;
            // remove from size map at the old size element
            map<int,set<int> >::iterator gotsize = size.find(old_size);
            gotsize->second.erase(*itera);
            if (gotsize->second.empty())
                size.erase(old_size);
            
            // place it at the right element in the size map (with the old size decreased by 1)
            --pags[i].embeddings[*itera].size;
            int new_size = pags[i].embeddings[*itera].size;
            gotsize = size.find(new_size);
            if (gotsize == size.end()) { // not in map
                set<int> temp;
                temp.insert(*itera);
                size.insert(pair<int,set<int> >(new_size, temp));
            } else size[new_size].insert(*itera);
        }
        
        //            // debug
        //            cout<<size.size()<<endl;
        //            map<int,set<int> >::iterator itrat;
        //            for (itrat = size.begin(); itrat != size.end(); itrat++)
        //                cout<<itrat->first<<" ";
        //            cout<<endl;
        //            cout<<size.begin()->first<<endl;
        //            //--
    }
    
    // save the VD-embeddings
    pags[i].vd_embeddings.max_degree = 0;
    
    map<int, set<int> >::iterator itervd;
    
    for (itervd = size.begin(); itervd != size.end(); itervd++) {
        set<int> temp = itervd->second;
        set<int>::iterator itr;
        for (itr = temp.begin(); itr != temp.end(); itr++) {
            pags[i].vd_embeddings.vd_embeddings.insert(pair<int, set<int> >(*itr, pags[i].embeddings[*itr].edges));
            if (pags[i].embeddings[*itr].max_degree > pags[i].vd_embeddings.max_degree) {
                pags[i].vd_embeddings.max_degree = pags[i].embeddings[*itr].max_degree;
                pags[i].vd_embeddings.max_count = 1;
            } else if (pags[i].embeddings[*itr].max_degree == pags[i].vd_embeddings.max_degree)
                pags[i].vd_embeddings.max_count++;
        }
    }
}

void Security::find_subgraphs() {
    set<int> not_permitted;
    
    for (int i = 0; i < igraph_ecount(G); i++) {
        // Create the subgraph
        set<int> current_subgraph;
        set<int>::iterator got = current_subgraph.find(i);
        if (got == current_subgraph.end()) // not in set
            current_subgraph.insert(i);
        
        set<int> neighbors;
        set<int> permitted_neighbors;
        
        if (maxPAGsize > 1) {
            // Enumerate the neighbors of the edge already in the subgraph. This will reduce the complexity of adding the neighbors of a newly added edge to the list of possible edges
            neighbors = edge_neighbors[i];
            
            // When we start, every edge we add is not permitted in the future
            set<int>::const_iterator got2 = not_permitted.find(i);
            if (got2 == not_permitted.end()) // not in set
                not_permitted.insert(i);
            
            //        // debug
            //        cout<<setfill('-')<<setw(100)<<"subgraphs enumaration"<<setfill('-')<<setw(99)<<"-"<<endl;
            //        cout<<i<<":";
            //        //--
            
            // add the neighbors of the edge to the possible edges
            set<int>::iterator it;
            for (it = edge_neighbors[i].begin(); it != edge_neighbors[i].end(); it++) {
                set<int>::iterator got = not_permitted.find(*it);
                // if it is permitted (not not permitted) then we can add it
                if (got == not_permitted.end()) { // not in set
                    set<int>::iterator got2 = permitted_neighbors.find(*it);
                    // If it's not already in the set add it -> security check
                    if (got2 == permitted_neighbors.end()) // not in set
                        permitted_neighbors.insert(*it);
                }
            }
        }
        
        //        // debug
        //        set<int>::iterator it2;
        //        for (it2 = permitted_neighbors.begin(); it2 != permitted_neighbors.end(); it2++)
        //            cout<<" "<<*it2;
        //        cout<<endl;
        //        //--
        
        // start constructing subgraphs of size maxPAGsize
        subgraphs(i, current_subgraph, permitted_neighbors, neighbors);
    }
    
    if (maxPAGsize == 0) {
        for (int i = 0; i < igraph_vcount(G); i++) {
            int color = VAN(G,"colour",i);
            map<int,vector<int> >::iterator got = colors.find(color);
            if (got == colors.end()) { // not in set
                // new pag
                vector<int> tmp;
                tmp.push_back(i);
                colors.insert(pair<int, vector<int> >(color, tmp));
            } else colors[color].push_back(i);
        }
    }
}

void Security::update_pags() {
    // for every pag...
    int pag_loop = pags.size() - 1;
    for (int i = pag_loop; i >= 0; i--) {
        int to_remove = pags[i].embeddings.size()-1;
        int loop = pags[i].embeddings.size() - 1;
        // .. for every embedding
        for (int j = loop; j >= 0 ; j--) {
            bool remove = false;
            set<int>::iterator it;
            int to_remove = -1;
            // see if any of its vertices was removed when copying the vd-embeddings to H
            for (it = pags[i].embeddings[j].vertices.begin(); it != pags[i].embeddings[j].vertices.end(); it++) {
                if (VAN(G, "Removed", *it) == Removed) { // if it removed
                    to_remove = j;
                    remove = true;
                    break;
                }
            }
            
            // if it was, remove it from the embeddings and from the vd-embeddings // delete as well
            if (remove)
                pags[i].embeddings.erase(pags[i].embeddings.begin()+j);
        }
        
        // the pag is a part of the embeddings, so if it's 0 then the pag should be removed
        if (pags[i].embeddings.size() == 0)
            pags.erase(pags.begin()+i);
        else { // if not
            bool remove = false;
            set<int>::iterator it;
            for (it = pags[i].vertices.begin(); it != pags[i].vertices.end(); it++) {
                if (VAN(G, "Removed", *it) == Removed) { // if it removed
                    remove = true;
                    break;
                }
            }
            
            // if the pag itself has a vertex that is removed then it is not in the embeddings anymore and so a new pag must be chosen
            if (remove == true) {
                // copy the information from the embedding to the pag
                pags[i].pag = pags[i].embeddings[0].edges;
                pags[i].vertices = pags[i].embeddings[0].vertices;
                pags[i].max_degree = pags[i].embeddings[0].max_degree;
                //pags[i].mapPAGG.clear(); // newremoved
                
                /*for (int j = 0; j < igraph_vector_size(pags[i].embeddings[0].map); j++)
                    pags[i].mapPAGG.insert(pair<int,int>(j,igraph_vector_e(pags[i].embeddings[0].map, j)));*/ // newremoved
                
                // delete the pag
                pags[i].embeddings.erase(pags[i].embeddings.begin()); // delete as well
            } else pags[i].embeddings.erase(pags[i].embeddings.end()-1); // If the pag is a vd-embedding then remove it from list of embeddings because we will add it back when searching for the VD-embeddings
        }
    }
}

void Security::VD_embeddings(int* max_degree, int* max_count, int* first_pag, int min_L1) {
    for (int i = 0; i < pags.size(); i++) {
        find_VD_embeddings(i);
        
        if (pags[i].vd_embeddings.vd_embeddings.size() >= min_L1) {
            if (pags[i].vd_embeddings.max_degree > *max_degree) {
                *max_degree = pags[i].vd_embeddings.max_degree;
                *max_count = pags[i].vd_embeddings.max_count;
                *first_pag = i;
            } else if (pags[i].vd_embeddings.max_degree == *max_degree) {
                if (pags[i].vd_embeddings.max_count > *max_count) {
                    *max_count = pags[i].vd_embeddings.max_count;
                    *first_pag = i;
                }
            }
        }
        
        // debug
        cout<<endl<<setw(100)<<setfill('-')<<"pags, embeddings, VD embeddings"<<setfill('-')<<setw(99)<<"-"<<endl;
        cout<<"pag #"<<i<<": ";
        set<int>::iterator iter;
        for (iter = pags[i].pag.begin(); iter != pags[i].pag.end(); iter++)
            cout<<*iter<<" ";
        cout<<endl;
        
        cout<<"vertices: ";
        for (iter = pags[i].vertices.begin(); iter != pags[i].vertices.end(); iter++)
            cout<<*iter<<" ";
        cout<<endl;
        
        for (int j = 0; j < pags[i].embeddings.size(); j++) {
            cout<<endl;
            cout<<"embeding #"<<j<<": ";
            set<int>::iterator iter2;
            for (iter2 = pags[i].embeddings[j].edges.begin(); iter2 != pags[i].embeddings[j].edges.end(); iter2++)
                cout<<*iter2<<" ";
            cout<<endl;
            cout<<"connected embeddings: ";
            set<int>::iterator it;
            for (it = pags[i].embeddings[j].connected_embeddings.begin(); it != pags[i].embeddings[j].connected_embeddings.end(); it++)
                cout<<*it<<" ";
            cout<<endl;
            cout<<"map: ";
            /*if (j != pags[i].embeddings.size()-1) {
                for (int k = 0; k < igraph_vector_size(pags[i].embeddings[j].map); k++)
                    cout<<igraph_vector_e(pags[i].embeddings[j].map, k)<<" ";
            }*/ // newremoved
            cout<<endl;
            cout<<"vertices: ";
            for (it = pags[i].embeddings[j].vertices.begin(); it != pags[i].embeddings[j].vertices.end(); it++)
                cout<<*it<<" ";
            cout<<endl;
            
            cout<<"max_deg: "<<pags[i].embeddings[j].max_degree<<endl;
        }
        
        cout<<endl;
        
        map<int, set<int> >::iterator iter2;
        cout<<"VD-embeddings: ";
        for (iter2 = pags[i].vd_embeddings.vd_embeddings.begin(); iter2 != pags[i].vd_embeddings.vd_embeddings.end(); iter2++)
            cout<<iter2->first<<" ";
        cout<<endl<<"max deg: "<<pags[i].vd_embeddings.max_degree<<" max count: "<<pags[i].vd_embeddings.max_count<<endl;
        
        for (iter2 = pags[i].vd_embeddings.vd_embeddings.begin(); iter2 != pags[i].vd_embeddings.vd_embeddings.end(); iter2++) {
            cout<<"embedding "<<iter2->first<<": ";
            set<int> temp = iter2->second;
            set<int>::iterator it;
            for (it = temp.begin(); it != temp.end(); it++)
                cout<<*it<<" ";
            cout<<"deg: "<<pags[i].embeddings[iter2->first].max_degree;
            cout<<endl;
        }
        //--
    }
}

void Security::get_vertex_neighbors() {
    for (int i = 0; i < igraph_vcount(G); i++) {
        set<int> neighbors;
        
        igraph_vector_t nvids; // deleted this
        igraph_vector_init(&nvids, 0);
        igraph_neighbors(G, &nvids, i, IGRAPH_OUT);
        
        for (int j = 0; j < igraph_vector_size(&nvids); j++)
            neighbors.insert(VECTOR(nvids)[j]);
        
        vertex_neighbors_out.push_back(neighbors);
        
        neighbors.clear();
        igraph_vector_clear(&nvids);
        igraph_neighbors(G, &nvids, i, IGRAPH_IN);
        
        for (int j = 0; j < igraph_vector_size(&nvids); j++)
            neighbors.insert(VECTOR(nvids)[j]);
        
        vertex_neighbors_in.push_back(neighbors);
        igraph_vector_destroy(&nvids); // new addition
    }
}

void Security::kiso(int min_L1, int max_L1, int maxPsize, int tresh, bool baseline) {
    // Initialization
    /*stringstream ss3;
    ss3 << min_L1;
    string str3 = ss3.str();

    for (int i = 0; i < 1000000000; i++)
        test.insert(i);
    //cout<<"yup"<<endl;
    string command = "ps u > usage_" + str3 + "_1.txt";
    system(command.c_str());
    
    test.clear();
    set<long>().swap(test);*/
    
    maxPAGsize = 0;
    
    edge_neighbors.clear();
    vector<set<int> >().swap(edge_neighbors);
    
    vertex_neighbors_in.clear();
    vector<set<int> >().swap(vertex_neighbors_in);
    
    vertex_neighbors_out.clear();
    vector<set<int> >().swap(vertex_neighbors_out);
    
    top_tier_vertices.clear();
    set<int>().swap(top_tier_vertices); //
    
    top_tier_edges.clear();
    map<int, set<int> >().swap(top_tier_edges); //
    
    pags.clear();
    vector<PAG>().swap(pags);
    
    colors.clear();
    map<int,vector<int> >().swap(colors); //
    
    H_v_dummy = 0;
    H_e_dummy = 0;
    G_v_lifted = 0;
    G_e_lifted = 0;
    start = false;
    
    //string command = "ps u > usage_" + str3 + "_2.txt";
    //system(command.c_str());
    
    clock_t tic = clock();
    maxPAGsize = maxPsize;
    
    int treshold = tresh == 0 ? 0 : min_L1/tresh;
    cout<<"treshold: "<<treshold<<endl;
    int G_ecount = igraph_ecount(G);
    int G_vcount = igraph_vcount(G);
    
    get_vertex_neighbors();
    
    while (igraph_vcount(G) != 0) {
        start = false;
        
      /*  for (int i = 0; i < pags.size(); i++)
            for (int j = 0; j < pags[i].embeddings.size(); j++)
                delete pags[i].embeddings[j].map; */ // newremoved
        
        pags.clear();
        pags = vector<PAG>();
        
        edge_neighbors.clear();
        edge_neighbors = vector<set<int> >();
        
        cout<<"PAG: "<<maxPAGsize<<endl;
        cout<<"G: "<<igraph_vcount(G)<<endl;
        cout<<"H: "<<igraph_vcount(H)<<endl;
        
        if (maxPAGsize > 1)
            get_edge_neighbors();
        
        //        // debug
        //        cout<<setfill('-')<<setw(100)<<"neighbors of edges"<<setfill('-')<<setw(99)<<"-"<<endl;
        //
        //        for (int i = 0; i < edge_neighbors.size(); i++) {
        //            cout<<i<<"'s neighbors:";
        //            set<int>::iterator it;
        //            for (it = edge_neighbors[i].begin(); it != edge_neighbors[i].end(); it++)
        //                cout<<" "<<*it;
        //            cout<<endl;
        //        }
        //        //--
        
        find_subgraphs();
        
        if (maxPAGsize == 0) {
//            cout<<"color size: "<<colors.size()<<endl;
            map<int, vector<int> >::iterator it;
            for (it = colors.begin(); it != colors.end(); it++) {
                vector<int> temp = it->second;
                
                //int multiple = temp.size()%min_L1;
                //int div = floor(temp.size()/min_L1);
//                cout<<"temp size: "<<temp.size()<<endl;
//                cout<<"tresh: "<<treshold<<endl;
                int loop = temp.size()-1;
                //int counter = 0;
                if (temp.size() >= min_L1) {
                    for (int i = loop; i >= 0; i--) {
                        //                    if (multiple != 0 && counter == div*min_L1)
                        //                        break;
                        
                        // add v to H
                        igraph_add_vertices(H, 1, 0);
                        int vid = igraph_vcount(H) - 1;
                        SETVAN(H, "colour", vid, VAN(G, "colour", temp[i]));
                        SETVAN(H, "ID", vid, VAN(G, "ID", temp[i]));
                        
                        // delete v from G
                        //                    igraph_vs_t id;
                        //                    igraph_vs_1(&id, temp[i]);
                        //                    igraph_delete_vertices(G,id);
                        SETVAN(G, "Removed", temp[i], Removed);
                        
                        SETVAS(F, "Tier", VAN(G, "ID", temp[i]), "Bottom");
                        SETVAS(R, "Tier", VAN(G, "ID", temp[i]), "Bottom");
                        // delete v from vector
                        temp.erase(temp.begin()+i);
                        
                        //counter++;
                    }
                } else {
                    //                if (multiple != 0) {
                    if (temp.size() >= treshold || baseline) {
                        // add
                        for (int i = min_L1-1; i >= 0; i--) {
                            // add v to H
                            igraph_add_vertices(H, 1, 0);
                            
                            int vid = igraph_vcount(H) - 1;
                            if (i < temp.size()) {
                                SETVAN(H, "colour", vid, VAN(G, "colour", temp[i]));
                                SETVAN(H, "ID", vid, VAN(G, "ID", temp[i]));
                                
                                // delete v from G
                                //                                igraph_vs_t id;
                                //                                igraph_vs_1(&id, temp[i]);
                                //                                igraph_delete_vertices(G,id);
                                SETVAN(G, "Removed", temp[i], Removed);
                                
                                SETVAS(F, "Tier", VAN(G, "ID", temp[i]), "Bottom");
                                SETVAS(R, "Tier", VAN(G, "ID", temp[i]), "Bottom");
                                // delete v from vector
                                temp.erase(temp.begin()+i);
                            } else {
                                H_v_dummy++;
                                
                                int tmp = it->first;
                                SETVAN(H, "colour", vid, tmp);
                                SETVAN(H, "ID", vid, vid);
                                
                                igraph_add_vertices(F, 1, 0);
                                SETVAS(F, "Tier", igraph_vcount(F) - 1, "Bottom");
                                SETVAN(F, "Dummy", igraph_vcount(F) - 1, kDummy);
                            }
                        }
                    } else {
                        loop = temp.size()-1;
                        for (int i = loop; i >= 0; i--) {
                            G_v_lifted++;
                            
                            set<int>::iterator has = top_tier_vertices.find(VAN(G, "ID",temp[i]));
                            if (has == top_tier_vertices.end()) // not in set
                                top_tier_vertices.insert(VAN(G, "ID", temp[i]));
                            
                            // delete v from G
                            //                            igraph_vs_t vid;
                            //                            igraph_vs_1(&vid, temp[i]);
                            //                            igraph_delete_vertices(G,vid);
                            SETVAN(G, "Removed", temp[i], Removed);
                            SETVAS(F, "Tier", VAN(G, "ID", temp[i]), "Top");
                            SETVAS(R, "Tier", VAN(G, "ID", temp[i]), "Top");
                            // delete v from vector
                            temp.erase(temp.begin()+i);
                        }
                    }
                }
            }
            
            int vcount = igraph_vcount(G) - 1;
            for (int i = vcount; i >= 0; i--) {
                if (VAN(G, "Removed", i) == Removed) {
                    igraph_vs_t vid;
                    igraph_vs_1(&vid, i);
                    igraph_delete_vertices(G,vid);
                    igraph_vs_destroy(&vid);
                }
            }
            
            continue;
        }
        
        // find the VD embeddings of every PAG
        int max_degree = 0;
        int max_count = 0;
        int first_pag = -1;
        //vector<vector<int> > VM; // newremoved
        
       /* for (int i = 0; i < min_L1; i++) {
            vector<int> temp;
            VM.push_back(temp);
        }*/ // newremoved
        
        do {
            max_degree = 0;
            max_count = 0;
            first_pag = -1;
            
            VD_embeddings(&max_degree, &max_count, &first_pag, min_L1);
            
            cout<<endl<<setfill('-')<<setw(100)<<"Add embeddings to H"<<setfill('-')<<setw(99)<<"-"<<endl;
            cout<<"first: "<<first_pag<<endl;
            
            if (first_pag == -1)
                continue;
            
            if (pags[first_pag].vd_embeddings.vd_embeddings.size() >= min_L1) {
                pags[first_pag].processed = true;
                //int multiple = pags[first_pag].vd_embeddings.vd_embeddings.size()%min_L1;
                map<int, set<int> >::iterator itr;
                int counter = 0;
                // for every vd-embedding
                for (itr = pags[first_pag].vd_embeddings.vd_embeddings.begin(); itr != pags[first_pag].vd_embeddings.vd_embeddings.end(); itr++) {
                    // if we have a multiple of k vd-embeddings, go through all of them
                    //                    if (multiple == 0) {
                    //                        if (counter == pags[first_pag].vd_embeddings.vd_embeddings.size())
                    //                            break;
                    //                    } else {
                    //                        // if we have a non multiple, we take min_L1 embeddings. If the non multiple is bigger than x*L1_min then we take x*L1_min embeddings
                    //                        int div = floor(pags[first_pag].vd_embeddings.vd_embeddings.size()/min_L1);
                    //                        if (counter == div*min_L1)
                    //                            break;
                    //                    }
                    
                    cout<<"embedding added to H: "<<itr->first<<endl;
                    
                    //map<int,int> mapGH;
                    set<int> dummy;
                    int dum;
                    set<int> edges = itr->second;
                    
                    // add embedding to H
                    create_graph(H, edges, dummy, &dum, false);
                    counter++;
                    
                    /*****************************************************************
                     This works because the mapping saves the corresponding vertex in
                     an embedding for a pag in ascending order (0->end) do when going
                     through the vertices of the pag in that order we garentee that the
                     mapping is valid. Even if the pag is not in the vd-embeddings, if
                     we get the corresponding vertices for every vd-embed by taking
                     the mapping done between it and the pag, for every vd-embed, then
                     we garentee that every vertex in any embed that maps to vertex i
                     in the pag will map to the vertex of any vd_embed that also maps
                     to vertex i in the pag
                     ****************************************************************/
                    
                    // if it's an embedding of the pag, then the isomorphic test generated a mapping
                    /*if (itr->first != pags[first_pag].embeddings.size()-1)
                        // go through that mapping and get the id of the vertex in H and insert it in the corresponding column in VM
                        for (int i = 0; i < igraph_vector_size(pags[first_pag].embeddings[itr->first].map); i++) {
                            map<int,int>::iterator got = mapGH.find(igraph_vector_e(pags[first_pag].embeddings[itr->first].map, i));
                            VM[counter%min_L1].push_back(got->second);
                        }
                    else { // if it's the pag itself, no mapping was created other than the one I did
                        map<int,int>::iterator it;
                        // go through that mapping and get the id of the vertex in H and insert in the corresponding column in VM
                        for (it = pags[first_pag].mapPAGG.begin(); it != pags[first_pag].mapPAGG.end(); it++) {
                            map<int,int>::iterator got = mapGH.find(VAN(G,"ID",it->second));
                            VM[counter%min_L1].push_back(got->second);
                        }
                    }*/ // newremoved
                    
                    // debug
                   /* if (itr->first != pags[first_pag].embeddings.size()-1) {
                        cout<<"G H"<<endl;
                        for (int i = 0; i < igraph_vector_size(pags[first_pag].embeddings[itr->first].map); i++) {
                            map<int,int>::iterator got = mapGH.find(igraph_vector_e(pags[first_pag].embeddings[itr->first].map, i));
                            cout<<got->first<<" "<<got->second<<endl;
                        }
                    } else {
                        cout<<"G H pag"<<endl;
                        map<int,int>::iterator it;
                        //cout<<pags[first_pag].mapPAGG.size();
                        for (it = pags[first_pag].mapPAGG.begin(); it != pags[first_pag].mapPAGG.end(); it++) {
                            map<int,int>::iterator got = mapGH.find(VAN(G,"ID",it->second));
                            cout<<got->first<<" "<<got->second<<" "<<it->first<<endl;
                        }
                    }*/ // newremoved
                    //--
                }
                
                // Update PAGs
                update_pags();
            }
        } while (first_pag != -1);
        
        if (!baseline) {
            cout<<endl<<setfill('-')<<setw(100)<<"Anonimyze"<<setfill('-')<<setw(99)<<"-"<<endl;
            
            while (!pags.empty()) {
                start = false;
                map<int,vector<int> > vd_embeddings;
                // find the pag that has the most vd-embeddings left
                for (int i = 0; i < pags.size(); i++) {
                    int vd_size = pags[i].vd_embeddings.vd_embeddings.size();
                    
                    map<int,vector<int> >::iterator got = vd_embeddings.find(vd_size);
                    if (got == vd_embeddings.end()) { // not in set
                        vector<int> temp;
                        temp.push_back(i);
                        vd_embeddings.insert(pair<int,vector<int> >(vd_size, temp));
                    } else vd_embeddings[vd_size].push_back(i);
                }
                
                map<int,vector<int> >::iterator got = vd_embeddings.end();
                got--;
                
                int pag = got->second[got->second.size() - 1];
                got->second.erase(got->second.begin() + got->second.size() - 1);
                if (got->first >= treshold) {
                    cout<<endl<<setfill('-')<<setw(100)<<"Add embeddings to H"<<setfill('-')<<setw(99)<<"-"<<endl;
                    cout<<"pag #"<<pag<<endl;
                    map<int,set<int> >::iterator it;
                    it = pags[pag].vd_embeddings.vd_embeddings.begin();
                    
                    for (int i = 0; i < min_L1; i++) {
                        if (it == pags[pag].vd_embeddings.vd_embeddings.end()) {
                            it = pags[pag].vd_embeddings.vd_embeddings.begin();
                            start = true;
                        }
                        
                        cout<<"embedding added to H: "<<it->first<<endl;
                        set<int>::iterator itr;
                        for (itr = it->second.begin(); itr != it->second.end(); itr++)
                            cout<<*itr<<" ";
                        cout<<endl;
                        //map<int,int> mapGH;
                        set<int> dummy;
                        int dum;
                        set<int> edges = it->second;
                        // add embedding to H
                        create_graph(H, edges, dummy, &dum, false);
                        
                        cout<<"H vcount = "<<igraph_vcount(H)<<endl<<endl;
                        
                        it++;
                    }
                } else {
                    // lift those embeddings
                    cout<<endl<<setfill('-')<<setw(100)<<"Remove embeddings from H"<<setfill('-')<<setw(99)<<"-"<<endl;
                    cout<<"pag #"<<pag<<endl;
                    map<int,set<int> >::iterator it;
                    for (it = pags[pag].vd_embeddings.vd_embeddings.begin(); it != pags[pag].vd_embeddings.vd_embeddings.end(); it++) {
                        cout<<"embedding removed from H: "<<it->first<<endl;
                        set<int> removed;
                        set<int>::iterator itr;
                        for (itr = it->second.begin(); itr != it->second.end(); itr++) {
                            int from, to;
                            
                            igraph_edge(G,*itr,&from,&to);
                            
                            set<int>::iterator got = removed.find(from);
                            if (got == removed.end()) { // not in set
                                G_v_lifted++;
                                set<int>::iterator has = top_tier_vertices.find(VAN(G, "ID",from));
                                if (has == top_tier_vertices.end()) // not in set
                                    top_tier_vertices.insert(VAN(G, "ID",from));
                                removed.insert(from);
                            }
                            SETVAS(F, "Tier", VAN(G, "ID",from), "Top");
                            SETVAS(R, "Tier", VAN(G, "ID",from), "Top");
                            
                            got = removed.find(to);
                            if (got == removed.end()) { // not in set
                                G_v_lifted++;
                                set<int>::iterator has = top_tier_vertices.find(VAN(G, "ID",to));
                                if (has == top_tier_vertices.end()) // not in set
                                    top_tier_vertices.insert(VAN(G, "ID",to));
                                removed.insert(to);
                            }
                            SETVAS(F, "Tier", VAN(G, "ID", to), "Top");
                            SETVAS(R, "Tier", VAN(G, "ID", to), "Top");
                            
                            G_e_lifted++;
                            map<int, set<int> >::iterator in = top_tier_edges.find(VAN(G, "ID",from));
                            if (in == top_tier_edges.end()) { // not in set
                                set<int> tmp;
                                tmp.insert(VAN(G, "ID",to));
                                top_tier_edges.insert(pair<int, set<int> >(VAN(G, "ID",from), tmp));
                            } else in->second.insert(VAN(G, "ID",to));
                            
                            int eid;
                            igraph_get_eid(F, &eid, VAN(G, "ID",from), VAN(G, "ID",to), IGRAPH_DIRECTED, 0);
                            SETEAS(F, "Tier", eid, "Top");
                            SETEAS(R, "Tier", eid, "Top");
                            
                            SETVAN(G, "Removed", from, Removed);
                            SETVAN(G, "Removed", to, Removed);
                            SETEAN(G, "Removed", *itr, Removed);
                        }
                    }
                }
                
                // Upadate PAGs
                pags.erase(pags.begin() + pag); // delete as well
                update_pags();
                
                max_degree = 0;
                max_count = 0;
                first_pag = -1;
                
                VD_embeddings(&max_degree, &max_count, &first_pag, min_L1);
            }
        }
        
        // debug
        /*cout<<endl;
        cout<<"VM:"<<endl;
        for (int i = 0; i < VM.size(); i++)
            cout<<i<<" ";
        cout<<"columns"<<endl;
        
        for (int i = 0; i < VM[0].size(); i++) {
            for(int j = 0; j < VM.size(); j++)
                cout<<VM[j][i]<<" ";
            cout<<endl;
        }*/ // newremoved
        //--
        
        cout<<endl;
        
        int vcount = igraph_vcount(G) - 1;
        for (int i = vcount; i >= 0; i--) {
            if (VAN(G, "Removed", i) == Removed) {
                igraph_vs_t vid;
                igraph_vs_1(&vid, i);
                igraph_delete_vertices(G,vid);
                igraph_vs_destroy(&vid);
            }
        }
        
        int ecount = igraph_ecount(G) - 1;
        for (int i = ecount; i >= 0; i--) {
            if (EAN(G, "Removed", i) == Removed) {
                igraph_es_t eid;
                igraph_es_1(&eid, i);
                igraph_delete_edges(G,eid);
                igraph_es_destroy(&eid);
            }
        }
        maxPAGsize--;
        
        cout<<endl;
        cout<<"G ecount - H ecount = "<<G_ecount - igraph_ecount(H)<<endl;
        cout<<"H vcount = "<<igraph_vcount(H)<<endl;
        cout<<"G vcount = "<<igraph_vcount(G)<<endl;
        cout<<endl;
    }
    
    int oneBond = 0;
    set<int>::iterator it;
    for (it = top_tier_vertices.begin(); it != top_tier_vertices.end(); it++) {
        set<int>::iterator iter;
        for (iter = vertex_neighbors_out[*it].begin(); iter != vertex_neighbors_out[*it].end(); iter++) {
            set<int>::iterator got = top_tier_vertices.find(*iter);
            if (got == top_tier_vertices.end()) { // not in set
                oneBond++;
                // edge going from to to is crossing
                // edge already exists
                int eid = -1;
                igraph_get_eid(F, &eid, *it, *iter, IGRAPH_DIRECTED, 1);
                if (eid != -1) {
                    SETEAS(F, "Tier", eid, "Crossing");
                    SETEAS(R, "Tier", eid, "Crossing");
                }
            }
            else {
                set<int>::iterator has = top_tier_edges[*it].find(*iter);
                if (has == top_tier_edges[*it].end()) { // not in set
                    G_e_lifted++;
                    top_tier_edges[*it].insert(*iter);
                    // edge is in top tier
                    // edge already exists
                    int eid = -1;
                    igraph_get_eid(F, &eid, *it, *iter, IGRAPH_DIRECTED, 1);
                    if (eid != -1) {
                        SETEAS(F, "Tier", eid, "Top");
                        SETEAS(R, "Tier", eid, "Top");
                    }
                }
            }
        }
        
        for (iter = vertex_neighbors_in[*it].begin(); iter != vertex_neighbors_in[*it].end(); iter++) {
            set<int>::iterator got = top_tier_vertices.find(*iter);
            if (got == top_tier_vertices.end()) {// not in set
                oneBond++;
                // edge going to to from is crossing
                // edge already exists
                int eid = -1;
                igraph_get_eid(F, &eid, *iter, *it, IGRAPH_DIRECTED, 1);
                if (eid != -1) {
                    SETEAS(F, "Tier", eid, "Crossing");
                    SETEAS(R, "Tier", eid, "Crossing");
                }
            }
        }
    }
    
    int lifted_edges = G_ecount - (igraph_ecount(H) - H_e_dummy) - G_e_lifted;
    set_topV(G_v_lifted);
    set_topE(G_e_lifted);
    set_bottomV(igraph_vcount(H));
    set_bottomE(igraph_ecount(H));
    int twoBond = lifted_edges-oneBond;
    set_twoBondLiftedEdge(twoBond);
    set_oneBondLiftedEdge(oneBond);
    set_bonds(oneBond + 2*twoBond);
    
    cout<<endl<<setfill('-')<<setw(100)<<"Report"<<setfill('-')<<setw(99)<<"-"<<endl;
    cout<<"Security lvl: "<<min_L1<<endl;
    cout<<"G initial vertex count: "<<G_vcount<<endl;
    cout<<"G initial edge count: "<<G_ecount<<endl;
    cout<<"G final vertex count: "<<G_v_lifted<<endl;
    cout<<"G final edge count: "<<G_e_lifted<<endl;
    cout<<endl;
    cout<<"H final vertex count, with dummies: "<<igraph_vcount(H)<<endl;
    cout<<"H final edge count, with dummies: "<<igraph_ecount(H)<<endl;
    cout<<"H final vertex count, without dummies: "<<igraph_vcount(H) - H_v_dummy<<endl;
    cout<<"H final edge count, without dummies: "<<igraph_ecount(H) - H_e_dummy<<endl;
    cout<<endl;
    cout<<"Lifted edges: "<<lifted_edges<<endl;
    cout<<endl;
    
    //    // debug
    //
    //    for (int i = 0; i < pags.size(); i++ ){
    //        cout<<endl<<setw(100)<<setfill('-')<<"updated pags, embeddings, VD embeddings"<<setfill('-')<<setw(99)<<"-"<<endl;
    //        cout<<"pag #"<<i<<": ";
    //        set<int>::iterator iter;
    //        for (iter = pags[i].pag.begin(); iter != pags[i].pag.end(); iter++)
    //            cout<<*iter<<" ";
    //        cout<<endl;
    //        cout<<"map: ";
    //        map<int,int>::iterator itr;
    //        for (itr = pags[i].mapPAGG.begin(); itr != pags[i].mapPAGG.end(); itr++)
    //            cout<<itr->second<<" ";
    //        cout<<endl;
    //
    //        for (int j = 0; j < pags[i].embeddings.size(); j++) {
    //            cout<<"embeding #"<<j<<": ";
    //            set<int>::iterator iter2;
    //            for (iter2 = pags[i].embeddings[j].edges.begin(); iter2 != pags[i].embeddings[j].edges.end(); iter2++)
    //                cout<<*iter2<<" ";
    //            cout<<endl;
    //            cout<<"connected embeddings: ";
    //            set<int>::iterator it;
    //            for (it = pags[i].embeddings[j].connected_embeddings.begin(); it != pags[i].embeddings[j].connected_embeddings.end(); it++)
    //                cout<<*it<<" ";
    //            cout<<endl;
    //        }
    //
    //        map<int, set<int> >::iterator iter2;
    //        cout<<"VD-embeddings: ";
    //        for (iter2 = pags[i].vd_embeddings.vd_embeddings.begin(); iter2 != pags[i].vd_embeddings.vd_embeddings.end(); iter2++)
    //            cout<<iter2->first<<" ";
    //        cout<<endl<<"max deg: "<<pags[i].vd_embeddings.max_degree<<" max count: "<<pags[i].vd_embeddings.max_count<<endl;
    //
    //        for (iter2 = pags[i].vd_embeddings.vd_embeddings.begin(); iter2 != pags[i].vd_embeddings.vd_embeddings.end(); iter2++) {
    //            cout<<"embedding "<<iter2->first<<": ";
    //            set<int> temp = iter2->second;
    //            set<int>::iterator it;
    //            for (it = temp.begin(); it != temp.end(); it++)
    //                cout<<*it<<" ";
    //            cout<<"deg: "<<pags[i].embeddings[iter2->first].max_degree;
    //            cout<<endl;
    //        }
    //    }
    //
    //    cout<<setw(100)<<setfill('-')<<"initial subgraphs"<<setfill('-')<<setw(99)<<"-"<<endl;
    //    cout<<endl;
    //    set<int>::iterator it;
    //    for (it = not_permitted.begin(); it != not_permitted.end(); it++)
    //        cout<<*it<<" ";
    //    cout<<endl;
    //
    //    cout<<setw(100)<<setfill('-')<<"Pags and their embeddings"<<setfill('-')<<setw(99)<<"-"<<endl;
    //    for (int i = 0; i < pags.size(); i++) {
    //        cout<<endl;
    //        set<int>::iterator iter;
    //        for (iter = pags[i].pag.begin(); iter != pags[i].pag.end(); iter++)
    //            cout<<*iter<<" ";
    //        cout<<endl<<"   ";
    //        for (int j = 0; j < pags[i].embeddings.size(); j++) {
    //            set<int>::iterator iter2;
    //            for (iter2 = pags[i].embeddings[j].begin(); iter2 != pags[i].embeddings[j].end(); iter2++)
    //                cout<<*iter2<<" ";
    //            cout<<endl<<"   ";
    //        }
    //    }
    //    //--
    
    clock_t toc = clock();
    
    cout<<"Took: "<<(double) (toc-tic)/CLOCKS_PER_SEC<<endl;
    
    write_to_file(lifted_edges, G_vcount, G_ecount, G_v_lifted, G_e_lifted, igraph_vcount(H), igraph_ecount(H), igraph_vcount(H) - H_v_dummy, igraph_ecount(H) - H_e_dummy, (double) (toc-tic)/CLOCKS_PER_SEC, oneBond, twoBond, igraph_vcount(F), igraph_ecount(F));

    // debug
    
    cout<<"oneBond: "<<oneBond<<endl;
    cout<<"twoBond: "<<twoBond<<endl;
    cout<<"bonds: "<<oneBond + 2*twoBond<<endl;
    
    for (it = top_tier_vertices.begin(); it != top_tier_vertices.end(); it++)
        cout<<*it<<" ";
    cout<<endl;
    
    map<int, set<int> >::iterator itmap;
    for (itmap = top_tier_edges.begin(); itmap != top_tier_edges.end(); itmap++) {
        cout<<"edge: "<<itmap->first<<": ";
        set<int> tmp = itmap->second;
        set<int>::iterator itset;
        for (itset = tmp.begin(); itset != tmp.end(); itset++)
            cout<<*itset<<" ";
        cout<<endl;
    }

//    for (int i = 0; i < vertex_neighbors_out.size(); i++) {
//        set<int>::iterator it;
//        cout<<"vertex: "<<i<<endl;
//        for (it = vertex_neighbors_out[i].begin(); it != vertex_neighbors_out[i].end(); it++)
//            cout<<*it<<" ";
//        for (it = vertex_neighbors_in[i].begin(); it != vertex_neighbors_in[i].end(); it++)
//            cout<<*it<<" ";
//        cout<<endl;
//    }
    //--
    cout<<"top tier: "<<top_tier_vertices.size()<<endl;
}
///////////////
