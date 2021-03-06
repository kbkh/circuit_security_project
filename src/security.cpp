
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

#define DEBUG
//#define PRINT_SOLUTION
//#define MEASURE_TIME
//#define MEASURE_TIME_S1
#define USE_SOLNS
//#define NRAND
//#define VF2

using namespace formula;
using namespace std;

/************************************************************//**
                                                               * @brief
                                                               * @return            string representation of connective
                                                               * @version						v0.01b
                                                               ****************************************************************/
igraph_bool_t check_map (
                         const igraph_t *graph1,
                         const igraph_t *graph2,
                         const igraph_integer_t vid1,
                         const igraph_integer_t vid2,
                         void *arg)
{
    L1_struct *mapped = (L1_struct*) arg;
    if (vid2 == mapped->vid2) {
        //        if (mapped->mapped[vid2][vid1]) //
        //            cout << "reject vid2(" << vid2 << ") -> vid1(" << vid1 << ")" << endl;
        return !mapped->mapped[vid2][vid1];
    }
    return true;
};


/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
bool l1_edge_lt (const L1_Edge* rhs, const L1_Edge* lhs) {
    return rhs->L1_prev < lhs->L1_prev;
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
bool l1_edge_info_lt (const EdgeInfo &rhs, const EdgeInfo &lhs) {
    return rhs.max_degree < lhs.max_degree;
}



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
bool parse (string line, Circuit *G, int &L1, int &L0, Edge &edge) {
    
    boost::regex report_rx ("\\|V\\(G\\)\\|");
    
    if ( regex_search(line, report_rx) ) {
        
        boost::regex num_rx   ("\\d+");
        boost::regex VG_rx    ("\\|V\\(G\\)\\| = \\d+");
        boost::regex EG_rx    ("\\|E\\(G\\)\\| = \\d+");
        boost::regex L0_rx    ("L0 = \\d+");
        boost::regex L1_rx    ("L1 = \\d+");
        boost::regex edge_rx  ("<\\d+,\\d+>");
        
        boost::sregex_token_iterator VG_token   (line.begin(), line.end(), VG_rx, 0);
        boost::sregex_token_iterator EG_token   (line.begin(), line.end(), EG_rx, 0);
        boost::sregex_token_iterator L0_token   (line.begin(), line.end(), L0_rx, 0);
        boost::sregex_token_iterator L1_token   (line.begin(), line.end(), L1_rx, 0);
        boost::sregex_token_iterator Edge_token (line.begin(), line.end(), edge_rx, 0);
        boost::sregex_token_iterator end;
        string token;
        
        assert (VG_token != end);
        {
            token = *VG_token;
            boost::sregex_token_iterator num(token.begin(), token.end(), num_rx, 0);
            assert (num != end);
            if ((int) igraph_vcount(G) != atoi(string(*num).c_str())) {
                cout << "|V(G)| = " << (int) igraph_vcount(G) << ", |V(G)| = " << atoi(string(*num).c_str()) << endl;
            }
            assert ( (int) igraph_vcount(G) == atoi(string(*num).c_str()) );
        }
        
        assert (EG_token != end);
        {
            token = *EG_token;
            boost::sregex_token_iterator num(token.begin(), token.end(), num_rx, 0);
            assert (num != end);
            assert ( (int) igraph_ecount(G) == atoi(string(*num).c_str()) );
        }
        
        if (L0_token != end) {
            token = *L0_token;
            boost::sregex_token_iterator num(token.begin(), token.end(), num_rx, 0);
            num++; // L0 yeilds a num
            assert (num != end);
            L0 = atoi(string(*num).c_str());
        }
        
        if (L1_token != end) {
            token = *L1_token;
            boost::sregex_token_iterator num(token.begin(), token.end(), num_rx, 0);
            num++; // L1 yeilds a num
            assert (num != end);
            L1 = atoi(string(*num).c_str());
        } else {
            return false;
        }
        
        if (Edge_token != end) {
            token = *Edge_token;
            boost::sregex_token_iterator num(token.begin(), token.end(), num_rx, 0);
            assert (num != end);
            edge.first = atoi(string(*num).c_str());
            num++;
            assert (num != end);
            edge.second = atoi(string(*num).c_str());
        } else {
            return false;
        }
        
        return true;
    } else {
        return false;
    }
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
string report (igraph_vector_t *soln) {
    
    string output;
    stringstream out;
    
    out << "map21: ";
    for (unsigned int i = 0; i < igraph_vector_size(soln); i++)
        out << VECTOR(*soln)[i] << ", ";
    output = out.str();
    output = output.substr(0, output.size()-2) + "\n";
    
    return output;
}


/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
bool parse (string line, igraph_vector_t *soln) {
    
    boost::regex map_rx ("map21: ");
    
    if ( regex_search(line, map_rx, boost::match_continuous) ) {
        
        boost::regex num_rx ("\\d+");
        boost::sregex_token_iterator end;
        boost::sregex_token_iterator num(line.begin(), line.end(), num_rx, 0);
        num++; // map21 yeilds a num
        
        for (unsigned int i = 0; i < igraph_vector_size(soln); i++, num++) {
            assert (num != end);
            VECTOR(*soln)[i] = atoi(string(*num).c_str());
        }
        assert (num == end);
        return true;
    } else {
        return false;
    }
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
Security::Security (Circuit *_G, Circuit *_H)
{
    G = _G;
    H = _H;
    
    igraph_vector_int_init(&colour_G, igraph_vcount(G));
    igraph_vector_int_init(&colour_H, igraph_vcount(H));
    
    for (unsigned int i=0; i<igraph_vcount(G); i++)
        VECTOR(colour_G)[i] = (int) VAN(G, "colour", i);
    
    for (unsigned int i=0; i<igraph_vcount(H); i++)
        VECTOR(colour_H)[i] = (int) VAN(H, "colour", i);
    
    isosat = new Isosat(G, H, &colour_G, &colour_H, 0, 0, &igraph_compare_transitives, 0, 0);
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
void Security::clean_solutions () {
    for (int i = solutions.size()-1; i >= 0; i--) {
        //cout<<"here 1"<<endl;
        igraph_bool_t iso(false);
        igraph_test_isomorphic_map (G, H, &colour_G, &colour_H, 0, 0, &iso, NULL, solutions[i],
                                    &igraph_compare_transitives, 0, 0);
        //cout<<"here 2"<<endl;
        
        if (!iso) {
            igraph_vector_destroy(solutions[i]);
            //cout<<"here 3"<<endl;
            solutions.erase(solutions.begin()+i);
            //cout<<"here 4"<<endl;
        }
        
    }
}




/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
void Security::print_solutions () {
    cout << endl;
    cout << "I'm here!" << endl;
    
    cout <<  solutions.size();
    for (int i = 0; i < solutions.size(); i++) {
        cout << "map21: ";
        igraph_vector_print(solutions[i]);
    }
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
void Security::add_edge (int eid) {
    H->add_edge(G->get_edge(eid));
    
    int from, to;
    igraph_edge(G, eid, &from, &to);
    igraph_get_eid(H, &eid, from, to, IGRAPH_DIRECTED, 1 /* error */);
    isosat->add_edge(G, H, eid, &colour_G, &colour_H, 0, 0, &igraph_compare_transitives, 0, 0);
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
int set_L1 (const Circuit *G, const vector<EdgeInfo> &edge_set) {
    
    vector<bool> from, to;
    for (unsigned int i=0; i<igraph_vcount(G); i++) {
        from.push_back(false);
        to.push_back(false);
    }
    
    int from_L1(0), to_L1(0);
    for (unsigned int i=0; i<edge_set.size(); i++) {
        Edge edge = edge_set[i].edge;
        if (!from[edge.first]) {
            from_L1++;
            from[edge.first] = true;
        }
        if (!to[edge.second]) {
            to_L1++;
            to[edge.second] = true;
        }
    }
    
    return min(from_L1, to_L1);
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            * precondition H is empty
                                                                            ****************************************************************************/
void Security::add_free_edges (int L1) {
    
    /******************************
     * Catorize edges
     ******************************/
    map<Edge, EdgeStats> edges;
    map<Edge, EdgeStats>::iterator it;
    
    for (unsigned int eid=0; eid<igraph_ecount(G); eid++) {
        Edge edge, colour;
        
        igraph_edge(G, eid, &edge.first, &edge.second);
        colour.first  = (int) VAN(G, "colour", edge.first);
        colour.second = (int) VAN(G, "colour", edge.second);
        
        it = edges.find(colour);
        if (it == edges.end()) edges[colour] = EdgeStats();
        
        edges[colour].unplaced.push_back( EdgeInfo(eid, edge, max(igraph_vertex_degree(G,edge.first), igraph_vertex_degree(G,edge.second)) ));
    }
    
    vector<bool> placed;
    for (unsigned int vid1 = 0; vid1 < igraph_vcount(G); vid1++)
        placed.push_back(false);
    
    
    
    /******************************
     * Add edges
     ******************************/
    it = edges.begin();
    while ( it != edges.end() ) {
        
        // removed partialy placed edges
        int i=0;
        while (i < (*it).second.unplaced.size() && (*it).second.unplaced.size() > 0) {
            Edge edge = (*it).second.unplaced[i].edge;
            if (placed[edge.first] || placed[edge.second]) {
                (*it).second.unplaced.erase((*it).second.unplaced.begin()+i);
                i = 0;
                continue;
            }
            i++;
        }
        sort((*it).second.unplaced.begin(), (*it).second.unplaced.end(), l1_edge_info_lt);
        reverse((*it).second.unplaced.begin(), (*it).second.unplaced.end());
        
        // pick edges to add
        for (unsigned int index = 0; index < (*it).second.unplaced.size(); index++) {
            
            if ( set_L1(G, (*it).second.unplaced) + (*it).second.placed.size() < L1 ) {
                break;
            }
            
            vector<EdgeInfo> test_set = (*it).second.unplaced;
            EdgeInfo test_edge = test_set[index];
            test_set.erase(test_set.begin()+index);
            int from = test_edge.edge.first; int to = test_edge.edge.second;
            
            for (unsigned int i = 0; i < test_set.size(); i++) { // remove an edge if it's like the one erased just earlier
                if (test_set[i].edge.first   == from || test_set[i].edge.first   == to ||
                    test_set[i].edge.second  == from || test_set[i].edge.second  == to) {
                    test_set.erase(test_set.begin()+i);
                    i = -1;
                }
            }
            
            if ((*it).second.placed.size() + set_L1(G, test_set) >= L1) {
                (*it).second.placed.push_back(test_edge);
                (*it).second.unplaced = test_set;
            }
            
        }
        //cout << "L1 = " << L1 << ", L1_set = " << set_L1(G, (*it).second.unplaced) << ", placed.size() = " << (*it).second.placed.size() << endl;
        // add edges
        for (unsigned int i = 0;  i < (*it).second.placed.size(); i++) {
            add_edge((*it).second.placed[i].eid);
            placed[(*it).second.placed[i].edge.first]  = true;
            placed[(*it).second.placed[i].edge.second] = true;
            string output;
            output = "S1_4free ("  + G->get_name() + ")";
            output = report(output, G, H, L1, 0, (*it).second.placed[i].edge);
            cout << output;
        }
        it++;
    }
    
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            run circuits/c17.blif tech_lib/minimal.genlib -w tmp -t -1
                                                                            ****************************************************************************/
bool Security::L0 (int max_count, bool quite) {
    if (!quite) {
        cout << " L0(" << max_count << "): ";
        cout.flush();
    }
    
    int count = 0;
    igraph_bool_t iso(true);
    while (iso && count < max_count) {
        igraph_vector_t map21;
        igraph_vector_init(&map21, igraph_vcount(H));
        isosat->solve(&iso, NULL, &map21);
        if (iso) {
            isosat->negate(NULL, &map21);
            count++;
            if (!quite) {
                cout << '*';
                cout.flush();
            }
        } else {
            return false;
        }
        igraph_vector_destroy(&map21);
    }
    return true;
}


/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
void Security::L1 (string label) {
    //cout << "L1(label): " << label << endl;
    int index(-1);
    for (unsigned int i=0; i<igraph_vcount(G); i++) {
        //cout << VAS(G, "label", i) << endl;
        if ( VAS(G, "label", i) == label ) {
            index = i;
            //cout << "index found: " << index << endl;
        }
    }
    
    vec<Lit> reject;
    igraph_bool_t iso(true);
    while (iso) {
        
        igraph_vector_t map21;
        igraph_vector_init(&map21, igraph_vcount(H));
        
        iso = false;
        isosat->solve(&iso, NULL, &map21, &reject);
        
        if (iso) {
            reject.push( isosat->translate(M21(index, VECTOR(map21)[index], true)) );
            cout << label << " -> " << VAS(G, "label", VECTOR(map21)[index]) << endl;
        }
        
        igraph_vector_destroy(&map21);
    }
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
int Security::L1 (bool quite, bool vf2) {
    //cout<<"HEREEEEEE"<<endl;
    /******************************
     * Setup
     ******************************/
    L1_struct L1_state;
    for (unsigned int i = 0; i < igraph_vcount(H); i++) {
        L1_state.mapped.push_back( vector<bool>() );
        for (unsigned int j = 0; j < igraph_vcount(G); j++) {
            L1_state.mapped.back().push_back(false);
        }
        L1_state.reject.push_back( new vec<Lit>() );
        //Added by Karl
        L1_state.infinite.push_back(false);
        ///////////////
    }
    
    
    /******************************
     * Check all previously found solutions
     ******************************/
    cout<<"solution: "<< solutions.size()<<endl;
    for (unsigned int vid2 = 0; vid2 < igraph_vcount(H); vid2++) {
        for (unsigned int k=0; k < solutions.size(); k++) {
            if (L1_state.mapped[vid2][VECTOR(*solutions[k])[vid2]] == false) {
                L1_state.mapped[vid2][VECTOR(*solutions[k])[vid2]] = true;
                L1_state.reject[vid2]->push( isosat->translate(M21(vid2, VECTOR(*solutions[k])[vid2], true)) );
                //Added by Karl
                if (VAN(H,"Lifted",vid2) == Lifted) {
                    L1_state.infinite[vid2] = true;
                }
                ///////////////
                if (L1_state.reject[vid2]->size() == igraph_vcount(G))
                    break;
            }
        }
    }
    
    
    /******************************
     * Find level
     ******************************/
    if (!quite) {
        cout << "L1(" << G->max_L1() << "): ";
        cout.flush();
    }
    
    // Added by Mohamed
    eliminate();
    ///////////////////
    
    for (unsigned int level = G->max_L1(); level > 1; level--) {
        //cout<<"level : "<<level<<endl;
        if ( L1(level, true, &L1_state, vf2) ) {
            //Added by Karl
            if (level == G->max_L1()) { // If level != max_L1() then noway the graph is inf-secure because this means a vertex has return false once and that shouldn't happen if it has an infinite vertex mapping because it would stop generating the mapping and thus it won't know when no more mappings are possible
                //bool infinite = true;
                for (int i = 0; i < L1_state.infinite.size(); i++)
                    if (L1_state.infinite[i] == false) //{ // If a vertex has sec level = max sec level and not infinite sec lvl
                        //infinite = false; // The graph is not inf sec
                        return level; // it is level-secure
                //}
                //if (infinite) {
                return -2; // -2 = inf lvl of sec
                //}
            }
            ///////////////
            
            return level;
        }
        if (!quite) {
            cout << '*' << level;
            cout.flush();
        }
    }
    return 1;
    
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
int Security::vf2_solve (igraph_bool_t *iso, igraph_vector_t *map12, igraph_vector_t *map21, L1_struct *mapped) {
    
    L1_Thread thread;
    thread.open(true, false);
    
    /******************************
     * Child
     ******************************/
    if (thread.child()) {
        igraph_subisomorphic_vf2(G, H, &colour_G, &colour_H, 0, 0, iso, map12, map21, &check_map, 0, mapped);
        string output = report(map21);
        igraph_vector_destroy(map21);
        thread.write(output);
        thread.close(false, true);
        _exit(0);
    }
    
    /******************************
     * Parent
     ******************************/
#define MAX_COUNT 10000
    bool finished(false);
    for (unsigned int i=0; i < MAX_COUNT; i++) {
        string response = thread.read();
        if (response.size() > 0) {
            parse(response, map21);
            if (VECTOR(*map21)[0] == 0 && VECTOR(*map21)[1] == 0)
                *iso = false;
            else
                *iso = true;
            finished = true;
            break;
        }
        usleep(1000);
    }
    
    if (!finished) {
        *iso = false;
        thread.close(true, false);
        thread.kill();
    }
    
    return 0;
}



/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
bool Security::L1 (int max_count, bool quite, L1_struct *_L1_state, bool vf2) {
    //cout<<"H"<<endl;
    if (vf2 && isosat != NULL) {
        delete isosat;
        isosat = NULL;
    }
    
    if (max_count > igraph_vcount(G))
        return false;
    
    /******************************
     * Setup
     ******************************/
    L1_struct *L1_state;
    if (_L1_state == NULL) {
        L1_state = new L1_struct();
        for (unsigned int i = 0; i < igraph_vcount(H); i++) {
            L1_state->mapped.push_back( vector<bool>() );
            for (unsigned int j = 0; j < igraph_vcount(G); j++) {
                L1_state->mapped.back().push_back(false);
            }
            L1_state->reject.push_back( new vec<Lit>() );
            //Added by Karl
            L1_state->infinite.push_back(false);
            ///////////////
        }
    } else {
        L1_state = _L1_state;
    }
    
    if (!quite) {
        cout << " L1(" << max_count << "): ";
        cout.flush();
    }
    
    /******************************
     * Run tests
     ******************************/
    //cout<<"max_count "<<max_count<<endl;
    bool result(true);
    for (unsigned int l = 2; l <= max_count; l++) {
        
        /******************************
         *
         ******************************/
        igraph_vector_t *map21 = new igraph_vector_t;
        igraph_vector_init(map21, igraph_vcount(H));
        
        int count = 0;
        for (unsigned int vid2 = 0; vid2 < igraph_vcount(H); vid2++) { // ... for every vertex in G check if there can be a mapping with all the old mappings
            //cout<<"A"<<endl;
            // Added by Mohamed
            //if (VAN(H, "consider", vid2)) continue;
            count++;
            //cout<<"1 v: "<<vid2<<" l: "<<l<<endl;
            //cout<<"vid2 "<<vid2<<endl;
            //if (L1_state->reject[vid2]->size() < l && !L1_state->infinite[vid2]) { //Added by Karl: || !L1_state->infinite[vid2] ... if this vertex has more mappings that the max level of security then we don't need to compute its mapping because the lvl of sec if the min of mappings amongst all the vertices.
            //cout<<"condition "<<(L1_state->reject[vid2]->size() < l)<<" "<< L1_state->infinite[vid2]<<endl;
            //cout<<"vertex : "<<vid2<<" Lifted? "<<L1_state->infinite[vid2]<<endl;
            if (!(L1_state->reject[vid2]->size() >= l || L1_state->infinite[vid2]) == Lifted) {
                //cout<<"2 v: "<<vid2<<" l: "<<l<<endl;
                // update count and reject list
                igraph_bool_t iso(false);
                
                if (vf2) {
                    L1_state->vid2 = vid2;
                    vf2_solve(&iso, NULL, map21, L1_state);
                } else {
                    isosat->solve(&iso, NULL, map21, L1_state->reject[vid2]); // ... mapping done here. If no mapping is possible considering the assumptions then iso = false and we stop.
                }
                // Added by Karl
                //cout<<"iso "<<iso<<endl;
                ////////////////
                //cout<<"vertex: "<<vid2<<"level: "<<l<<endl;
                if (iso) {
#ifndef NDEBUG
                    igraph_bool_t test_iso(false);
                    igraph_test_isomorphic_map (G, H, &colour_G, &colour_H, 0, 0, &test_iso, NULL, map21,
                                                &igraph_compare_transitives, 0, 0);
                    if (!test_iso) {
                        H->print();
                        igraph_vector_print(map21);
                    }
                    assert(test_iso);
#endif
                    assert ( L1_state->mapped[vid2][VECTOR(*map21)[vid2]] == false );
                    // v_G = vid2; v_H = VECTOR(*map21)[vid2]
                    // if v_H is lifted then v_G has inf security level;
                    // Added by Karl
                    //cout<<"map "<<VECTOR(*map21)[vid2]<<endl;
                    //cout<<"Lifted "<<VAN(H,"Lifted",vid2)<<endl;
                    //cout<<"3 v: "<<vid2<<" l: "<<l<<endl;
                    if (VAN(H,"Lifted",vid2/*VECTOR(*map21)[vid2]*/) == Lifted)
                        L1_state->infinite[vid2] = true;
                    
                    //cout<<max_count<<" "<<vid2<<" "<<L1_state->infinite[vid2]<<endl;
                    ////////////////
                    
                    solutions.push_back(map21); // ... mapping is good.
                    for (unsigned int i = 0; i < igraph_vector_size(map21); i++) {
                        if (L1_state->mapped[i][VECTOR(*map21)[i]] == false) {
                            L1_state->mapped[i][VECTOR(*map21)[i]] = true;
                            if (vf2)
                                L1_state->reject[i]->push( mkLit(0) );
                            else
                                L1_state->reject[i]->push( isosat->translate(M21(i, VECTOR(*map21)[i], true))); // ... ++ at every mapping that works + assumption for the solver
                            // i v in H, the other one is v in G
                        }
                    }
                    map21 = new igraph_vector_t;
                    igraph_vector_init(map21, igraph_vcount(H));
                } else {
                    // Added by Karl
                    //write_levels(vid2,l);
                    ////////////////
                    if (_L1_state == NULL)
                        delete L1_state;
                    return false;
                }
                
            }
        }
        
        //cout << endl << count << endl; //cout.flush();
        
        igraph_vector_destroy(map21);
        
        if (!quite) {
            cout << '*';
            cout.flush();
        }
    }
    if (_L1_state == NULL)
        delete L1_state;
    
    return true;
}

void Security::eliminate()
{
    
    // H->print(cout);
    // cout.flush();
    igraph_vector_ptr_t components;
    
    // if (igraph_decompose(H, components, IGRAPH_WEAK, -1, 1) != IGRAPH_ENOMEM)
    // ;
    
    igraph_vector_t membership, csize;
    
    igraph_vector_init(&membership, 1);
    
    igraph_vector_init(&csize, 1);
    igraph_integer_t no;
    
    igraph_clusters(H, &membership, &csize, &no, IGRAPH_WEAK);
    igraph_vector_ptr_init(&components, no);
    
    
    
    igraph_vector_ptr_t colour_vecs;
    igraph_vector_ptr_init(&colour_vecs, no);
    
    //		cout << endl << no << "components" << endl;
    
    for (int i = 0; i < no; i++)
    {
        igraph_vector_t members;
        igraph_vector_int_t colours;
        igraph_vector_init(&members, 0);
        // igraph_vector_int_init(&colours, 0);
        igraph_vector_ptr_set(&colour_vecs, i , malloc(sizeof(igraph_vector_int_t)));
        igraph_vector_int_init((igraph_vector_int_t*) VECTOR(colour_vecs)[i], 0);
        
        for (int j = 0; j < igraph_vector_size(&membership); j++)
        {
            if (igraph_vector_e(&membership, j) == i)
            {
                igraph_vector_push_back(&members, j);
                //					igraph_vector_int_push_back(&colours, VECTOR(colour_H)[j]);
                igraph_vector_int_push_back((igraph_vector_int_t*) VECTOR(colour_vecs)[i], VECTOR(colour_H)[j]);
            }
        }
        igraph_vs_t vs;
        igraph_vs_vector(&vs, &members);
        igraph_t res;
        //			cout << endl << "Members of component " << i << " are: ";
        //			for (int j = 0; j < igraph_vector_size(&members); j++)
        //				cout << VECTOR(members)[j] << " ";
        
        //			cout << endl;
        igraph_vector_ptr_set(&components, i , malloc(sizeof(igraph_t)));
        igraph_induced_subgraph(H, (igraph_t*) VECTOR(components)[i], vs, IGRAPH_SUBGRAPH_CREATE_FROM_SCRATCH);
        //			cout << igraph_vcount(&res) << " vertices in subgraph" << endl;
        //			igraph_vector_ptr_set(&components, i , &res);
        //			igraph_vector_ptr_set(&colour_vecs, i , &colours);
        igraph_vector_destroy(&members);
    }
    
    
    
    //		igraph_vector_ptr_t colour_vecs;
    //		igraph_vector_ptr_init(&colour_vecs, no);
    //
    //		for (int i = 0; i < igraph_vector_ptr_size(&components); i++)
    //		{
    //			igraph_vector_t res;
    //			igraph_vector_init(&res, 1);
    //			VANV((igraph_t*)igraph_vector_ptr_e(&components, i), "colour", &res);
    //			igraph_vector_ptr_set(&colour_vecs, i, &res);
    //		}
    
    //		for (int i = 0; i < igraph_vector_ptr_size(&components); i ++)
    //			cout << endl << "Number of vertices in component " << i << ": " << igraph_vcount((igraph_t*) VECTOR(components)[i]) << ", Colour vector size: " << igraph_vector_int_size((igraph_vector_int_t*) VECTOR(colour_vecs)[i]);
    
    //cout.flush();
    //		for (int i = 0; i < igraph_vector_size(&membership); i ++)
    //			cout << endl << VECTOR(membership)[i];
    
    igraph_vector_t consider;
    igraph_vector_init(&consider, igraph_vcount(H));
    
    SETVANV(H, "consider", &consider);
    
    igraph_vector_bool_t isomorphic;
    igraph_vector_bool_init(&isomorphic, no);
    for (int i = 0; i < igraph_vector_ptr_size(&components); i++)
    {
        for (int j = i+1; j < igraph_vector_ptr_size(&components); j++)
        {
            if (VECTOR(isomorphic)[j]) continue;
            igraph_bool_t iso;
            //				cout << "boo";cout.flush();
            if (igraph_vcount((igraph_t*)VECTOR(components)[i]) != igraph_vcount((igraph_t*)VECTOR(components)[j])
                || igraph_ecount((igraph_t*)VECTOR(components)[i]) != igraph_ecount((igraph_t*)VECTOR(components)[j])) continue;
            igraph_isomorphic_vf2((igraph_t*)VECTOR(components)[i], (igraph_t*) VECTOR(components)[j], (igraph_vector_int_t *) VECTOR(colour_vecs)[i], (igraph_vector_int_t *) VECTOR(colour_vecs)[j], NULL, NULL, &iso, NULL, NULL, 0, 0, NULL);
            if (iso)
            {
                igraph_vector_bool_set(&isomorphic, j, true);
                for (int k = 0; k < igraph_vector_size(&membership); k++)
                {
                    if (igraph_vector_e(&membership, k) == j)
                        SETVAN(H, "consider", k, 1);
                }
                //					igraph_destroy((igraph_t*)VECTOR(components)[j]);
                //					free(VECTOR(components)[j]);
                //					igraph_vector_ptr_remove(&components, j);
                //					igraph_vector_int_destroy((igraph_vector_int_t*) VECTOR(colour_vecs)[j]);
                //					free(VECTOR(colour_vecs)[j]);
                //					igraph_vector_ptr_remove(&colour_vecs, j);
                //					j--;
            }
        }
    }
    
    for (int i = 0; i < igraph_vector_ptr_size(&components); i++)
    {
        igraph_destroy((igraph_t*)igraph_vector_ptr_e(&components, i));
        //			igraph_vector_destroy((igraph_vector_t *) igraph_vector_ptr_e(&colour_vecs, i));
        //free(VECTOR(components)[j]);
        igraph_vector_int_destroy((igraph_vector_int_t*) VECTOR(colour_vecs)[i]);
    }
    igraph_vector_ptr_destroy_all(&components);
    igraph_vector_ptr_destroy_all(&colour_vecs);
    igraph_vector_destroy(&membership);
    igraph_vector_destroy(&csize);
    igraph_vector_destroy(&consider);
    
    //cout.flush();
}

/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            run circuits/c17.blif tech_lib/minimal.genlib -w tmp -t -1
                                                                            ****************************************************************************/
void Security::S1_rand (int threads, int min_L1, bool quite) { //2//true
    
    /******************************
     * Setup
     ******************************/
    vector<int> good;
    for (unsigned int eid = 0; eid < igraph_ecount(G); eid++) {
        //cout<<"test edge: "<<!H->test_edge(G->get_edge(eid))<<endl;
        if (!H->test_edge(G->get_edge(eid))) {
            good.push_back(eid);
        }
    }
    
#ifndef NRAND
    random_shuffle(good.begin(), good.end());
#endif
    
    vector<L1_Thread*> busy_threads, free_threads;
    for (unsigned int i=0; i<threads; i++)
        free_threads.push_back( new L1_Thread() );
    
    //cout<<"Free threads size: "<<free_threads.size()<<endl;
    
    
    /******************************
     * Add edges until L1 == min_L1
     ******************************/
    bool done(false);
    while (!done || busy_threads.size() > 0) {
        
        /******************************
         * Load Threads (create sub-processes)
         ******************************/
        if (!done && free_threads.size() > 0) {
            int test_index = good.back();
            good.pop_back();
            add_edge(test_index);
            
            busy_threads.push_back(free_threads.back());
            //cout<<"Busy threads size: "<<busy_threads.size()<<endl;
            free_threads.pop_back();
            //cout<<"Free threads size 1: "<<free_threads.size()<<endl;
            busy_threads.back()->open(true,false);
            
            /******************************
             * Child
             ******************************/
            if ( busy_threads.back()->child() ) {              // Child (PID == 0)
                
                Edge test_edge = G->get_edge(test_index);
                int test_L1 = L1();
                
                string output;
                output = "S1_rand ("  + G->get_name() + ").child(" + num2str(getpid()) + ")";
                output = report(output, G, H, test_L1, solutions.size(), test_edge);
                
#ifdef DEBUG
                cout << output << endl;
#endif
                
                //cout<<"Nothing to see here"<<endl;
                busy_threads.back()->write(output);
                //cout<<"Busy threads size1: "<<busy_threads.size()<<endl;
                busy_threads.back()->close(false, true);
                _exit(0);
            }
            
        }
        
        /******************************
         * Unload Threads (Parent)
         ******************************/
        do {
            //cout<<"YAALLLAAAAA: "<<endl<<endl<<endl;
            //cout<<"Busy threads size2: "<<busy_threads.size()<<endl;
            for (unsigned int j=0; j<busy_threads.size(); j++) {
                string response = busy_threads[j]->read();
                // do something with response
                if (response.size() > 0) {
                    
                    int L0, test_L1;
                    Edge test_edge;
                    
                    stringstream r_stream(response);
                    string line;
                    while( getline(r_stream, line) )
                        parse(line, G, test_L1, L0, test_edge);
                    
                    string output;
                    output = "S1_rand ("  + G->get_name() + ")";
                    output = report(output, G, H, test_L1, L0, test_edge);
                    cout << endl << output;
                    
                    free_threads.push_back(busy_threads[j]);
                    //cout<<"Free threads size 2: "<<free_threads.size()<<endl;
                    busy_threads.erase(busy_threads.begin()+j);
                    //cout<<"Busy threads size3: "<<busy_threads.size()<<endl;
                    
                    if (test_L1 < min_L1) done = true;
                }
            }
        } while (free_threads.size() == 0);
        //cout<<"YAALLLAAAAA1: "<<busy_threads.size()<<endl<<endl<<endl;
    }
}

void Security::S1_self()
{
    clean_solutions();
    cout << L1(false, false);
}

int C_SAT::e(int i) { return marker - igraph_ecount(self->G) + i; }

int C_SAT::phi(int u, int v, int i, int j) {
    Circuit* G = self->G;
    int color = VAN(G, "colour", u);
    int index = 0;
    int l;
    for (l = 0; l < color; l++)
    {
        int n = igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[l]);
        index += n * n * (igraph_vcount(G)) * (igraph_vcount(G));
    }
    bool found1 = false, found2 = false;
    int k1=-1, k2=-1;
    
    //	l = VAN()
    while (!found1 || !found2)
    {
        if (!found1) if (igraph_vector_e((igraph_vector_t*) VECTOR(match_vert)[l],++k1) == u) found1 = true;
        if (!found2) if (igraph_vector_e((igraph_vector_t*) VECTOR(match_vert)[l],++k2) == v) found2 = true;
    }
    //	k2 = v;
    index += ( k1 * (igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[l])) + k2 ) * igraph_vcount(G) * igraph_vcount(G) + i * igraph_vcount(G) + j;
    return index + 1;
}

Formula* C_SAT::leq( const vec<Formula*>& fvector, string n, int start)
{
    if (start == n.length()) return NULL;
    Formula* ret;
    int index = n.length() - start - 1;
    
    if (n[start]=='0')
    {
        ret = new Formula(F_AND);
        Formula * tmp = new Formula(F_AND), *neg = new Formula(*fvector[index]); neg->negate();
        ret->add(neg);
        ret->add(leq(fvector, n, ++start));
    }
    else
    {
        ret = new Formula(F_OR);
        Formula * tmp = new Formula(F_AND), *neg = new Formula(*fvector[index]); neg->negate();
        ret->add(neg);
        tmp->add(fvector[index]);
        tmp->add(leq(fvector, n, ++start));
        ret->add(tmp);
    }
    return ret;
}

Formula* C_SAT::leq( const vec<Var>& fvector, string n, int start)
{
    if (start == n.length()) return NULL;
    Formula* ret;
    int index = n.length() - start - 1;
    
    if (n[start]=='0')
    {
        ret = new Formula(F_AND);
        //Formula * tmp = new Formula(F_AND), *neg = new Formula(*fvector[index]); neg->negate();
        Lit neg = mkLit(fvector[index],true);
        ret->add(neg);
        ret->add(leq(fvector, n, ++start));
    }
    else
    {
        ret = new Formula(F_OR);
        Formula * tmp = new Formula(F_AND);//, *neg = new Formula(*fvector[index]); neg->negate();
        Lit neg = mkLit(fvector[index], true);
        ret->add(neg);
        tmp->add(mkLit(fvector[index]));
        tmp->add(leq(fvector, n, ++start));
        ret->add(tmp);
    }
    return ret;
}

Formula* C_SAT::geq( const vec<Formula*>& fvector, string n, int start)
{
    if (start == n.length()) return NULL;
    int index = n.length() - start - 1;
    Formula* ret;
    
    if (n[start]=='1')
    {
        ret = new Formula(F_AND);
        ret->add(fvector[index]);
        ret->add(geq(fvector, n, ++start));
    }
    else
    {
        ret = new Formula(F_OR);
        Formula * tmp = new Formula(F_AND), *neg = new Formula(*fvector[index]); neg->negate();
        ret->add(fvector[index]);
        tmp->add(neg);
        tmp->add(geq(fvector, n, ++start));
        ret->add(tmp);
    }
    
    return ret;
}

Formula* C_SAT::geq( const vec<Var>& fvector, string n, int start)
{
    if (start == n.length()) return NULL;
    int index = n.length() - start - 1;
    Formula* ret;
    
    if (n[start]=='1')
    {
        ret = new Formula(F_AND);
        ret->add(mkLit(fvector[index]));
        ret->add(geq(fvector, n, ++start));
    }
    else
    {
        ret = new Formula(F_OR);
        Formula * tmp = new Formula(F_AND);//, *neg = new Formula(*fvector[index]); neg->negate();
        Lit neg = mkLit(fvector[index],true);
        ret->add(mkLit(fvector[index]));
        tmp->add(neg);
        tmp->add(geq(fvector, n, ++start));
        ret->add(tmp);
    }
    
    return ret;
}

string C_SAT::convertInt(int number)
{
    if (number == 0)
        return "0";
    string temp="";
    string returnvalue="";
    while (number>0)
    {
        temp+=number%2+48;
        number/=2;
    }
    for (int i=0;i<temp.length();i++)
        returnvalue+=temp[temp.length()-i-1];
    return returnvalue;
}

C_SAT::C_SAT(Security* security, int min_L1, int max_L1, int eta) {
    
    self = security;
    Circuit* G = self->G;
    sat = new Formula(F_AND);
    igraph_vector_ptr_init(&match_vert, 0);
    for (int i = 0; i < igraph_vcount(G); i++)
    {
        int color = VAN(G, "colour", i);
        if (igraph_vector_ptr_size(&match_vert) < color + 1)
            for (int j = igraph_vector_ptr_size(&match_vert); j <= color; j++)
            {
                igraph_vector_t* v = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                igraph_vector_init(v, 0);
                igraph_vector_ptr_push_back(&match_vert, v);
            }
        igraph_vector_push_back((igraph_vector_t*) VECTOR(match_vert)[color], i);
    }
    
    for (int i=0; i < igraph_vector_ptr_size(&match_vert); i++)
    {
        for (int j=0; j < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[i]); j++)
            cout << igraph_vector_e((igraph_vector_t*) VECTOR(match_vert)[i], j) << "";
        cout << endl;
    }
    
    cout.flush();
    
    //	int nVars
    
    for (int i=0; i < igraph_vector_ptr_size(&match_vert); i++)
    {
        int n = igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[i]);
        for (int j=0; j < n * n * (igraph_vcount(G))*(igraph_vcount(G)); j++)
            sat->newVar();
    }
    
    for (int i=0; i < igraph_ecount(G); i++) sat->newVar();
    
    marker = sat->maxVar();
    
    int n = (int) floor(log(igraph_ecount(G))/log(2)+1);
    //	char* eta_b = (char*) malloc(n);
    
    string eta_b = convertInt(eta);
    string temp="";
    for (int i = eta_b.length(); i < n; i++)
        temp+='0';
    
    eta_b=temp+eta_b;
    vec<Formula*> sum;
    
    for (int i = 0; i < n; i++)
        sum.push(NULL);
    
    Formula* tmp1 = new Formula(), *tmp2 = new Formula(), *tmp3 = new Formula(), *carry = new Formula(), *sum_neg = new Formula(), *carry_neg = new Formula();
    tmp1->add(mkLit(e(1)));
    tmp1->add(mkLit(e(2), true));
    
    tmp2->add(mkLit(e(1), true));
    tmp2->add(mkLit(e(2)));
    
    sum[0] = new Formula(F_OR);
    sum[0]->add(tmp1);
    sum[0]->add(tmp2);
    
    carry->add(mkLit(e(1)));
    carry->add(mkLit(e(2)));
    
    sum[1] = carry;
    
    for (int i = 3; i <= igraph_ecount(G); i++)
    {
        sum_neg = new Formula(*sum[0]); sum_neg->negate();
        tmp1 = new Formula();
        tmp1->add(sum[0]);
        tmp1->add(mkLit(e(i), true));
        
        tmp2 = new Formula();
        tmp2->add(sum_neg);
        tmp2->add(mkLit(e(i)));
        
        carry = new Formula();
        carry->add(sum[0]);
        carry->add(mkLit(e(i)));
        
        sum[0] = new Formula(F_OR);
        sum[0]->add(tmp1);
        sum[0]->add(tmp2);
        
        int j;
        for (j = 1; sum[j]!=NULL && j < sum.size(); j++)
        {
            Formula* carry_neg = new Formula(*carry);
            sum_neg = new Formula(*sum[j]);
            
            sum_neg->negate(); carry_neg->negate();
            
            tmp1 = new Formula();
            tmp1->add(sum[j]);
            tmp1->add(carry_neg);
            
            tmp2 = new Formula();
            tmp2->add(sum_neg);
            tmp2->add(carry);
            
            tmp3 = new Formula();
            tmp3->add(sum[j]);
            tmp3->add(carry);
            
            sum[j] = new Formula(F_OR);
            sum[j]->add(tmp1);
            sum[j]->add(tmp2);
            
            carry = tmp3;
            
        }
        if (j < sum.size()) sum[j] = carry;
    }
    
    
    Formula* ecount_less_than_eta = leq(sum, eta_b, 0);
    //cout << ecount_less_than_eta->str();
    sat->add(ecount_less_than_eta);
    
    Formula* k_secure = new Formula(F_AND);
    
    
    //	vec<Formula*> formuli;
    for (int i = 0; i < igraph_vcount(G); i++)
    {
        int color = VAN(G, "colour", i);
        vec<Formula*> formuli;
        for (int j1 = 0; j1 < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[color]); j1++)
        {
            int j = igraph_vector_e((igraph_vector_t*) VECTOR(match_vert)[color], j1);
            Formula* F1 = new Formula(F_AND);
            for (int k = 0; k < igraph_vcount(G); k++)
            {	if (k == i) continue;
                int k_color = VAN(G, "colour", k);
                Formula* nested = new Formula(F_OR);
                //				for (int l = 0; l < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); l++)
                for (int l = 0; l < igraph_vcount(G); l++)
                {	if (l==j) continue;
                    Formula* nested1 = new Formula(F_AND);
                    int l_color = VAN(G, "colour", l);
                    if (k_color != l_color) continue;
                    if (k == i && l != j) continue;
                    if (k != i || l != j) nested1->add(mkLit(phi(i, j, k, l)));
                    
                    for (int h = 0; h < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); h++)
                        //					for (int h = 0; h < igraph_vcount(G); h++)
                    {
                        igraph_vector_t *vec = (igraph_vector_t *) VECTOR(match_vert)[k_color];
                        if (VECTOR(*vec)[h] != l && VECTOR(*vec)[h] != j) nested1->add(mkLit(phi(i, j, k, VECTOR(*vec)[h]), true));
                    }
                    nested->add(nested1);
                }
                F1->add(nested);
            }
            
            Formula* F2 = new Formula(F_AND);
            for (int k = 0; k < igraph_vcount(G); k++)
            {	if (k==j) continue;
                int k_color = VAN(G, "colour", k);
                Formula* nested = new Formula(F_OR);
                //for (int l = 0; l < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); l++)
                for (int l = 0; l < igraph_vcount(G); l++)
                {	if (l==i) continue;
                    Formula* nested1 = new Formula(F_AND);
                    int l_color = VAN(G, "colour", l);
                    if (k_color != l_color) continue;
                    if (k == j && l != i) continue;
                    if (k != j || l != i) nested1->add(mkLit(phi(i, j, l, k)));
                    
                    for (int h = 0; h < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); h++)
                    {
                        //					for (int h = 0; h < igraph_vcount(G); h++)
                        igraph_vector_t *vec = (igraph_vector_t *) VECTOR(match_vert)[k_color];
                        if (VECTOR(*vec)[h] != l && VECTOR(*vec)[h] != i) nested1->add(mkLit(phi(i, j, VECTOR(*vec)[h], k), true));
                    }
                    nested->add(nested1);
                }
                F2->add(nested);
            }
            
            Formula* F3 = new Formula(F_AND);
            for (int k = 0; k < igraph_ecount(G); k++)
            {
                //				F3->add(mkLit(e(k),true));
                Formula* nested = new Formula(F_OR);
                nested->add(mkLit(e(k+1)));
                for (int l = 0; l < igraph_ecount(G); l++)
                {
                    int src_l, dest_l, src_k, dest_k;
                    igraph_edge(G, l, &src_l, &dest_l);
                    int src_col_k, dest_col_k, src_col_l, dest_col_l;
                    src_col_l = VAN(G, "colour", src_l);
                    dest_col_l = VAN(G, "colour", dest_l);
                    //					if (src_col != dest_col) continue;
                    igraph_edge(G, k, &src_k, &dest_k);
                    src_col_k = VAN(G, "colour", src_k);
                    dest_col_k = VAN(G, "colour", dest_k);
                    if (src_col_l != src_col_k || dest_col_l != dest_col_k) continue;
                    //					if (src_k == i && src_l == j && dest_k == i && dest_l == j) break;
                    if (src_k == i && src_l != j || dest_k == i && dest_l != j) continue;
                    if (src_k != i && src_l == j || dest_k != i && dest_l == j) continue;
                    if (src_k == i && src_l == j) { nested->add(mkLit(phi(i,j,dest_k,dest_l))); continue; }
                    if (dest_k == i && dest_l == j) { nested->add(mkLit(phi(i,j,src_k,src_l))); continue; }
                    Formula* p = new Formula(F_AND);
                    p->add(mkLit(phi(i,j,src_k,src_l)));
                    p->add(mkLit(phi(i,j,dest_k,dest_l)));
                    nested->add(p);
                }
                F3->add(nested);
            }
            
            Formula* F = new Formula(F_AND);
            F->add(F1);
            F->add(F2);
            F->add(F3);
            formuli.push(F);
            if (i == 10 && j == 1) cout << F->str();
        }
        
        int n = (int) floor(log(igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[color]))/log(2)+1);
        //		char* min_L1_b = (char*) malloc(n);
        
        string min_L1_b = convertInt(min_L1);
        
        string temp="";
        for (int j = min_L1_b.length(); j < n; j++)
            temp+="0";
        min_L1_b=temp+min_L1_b;
        cout << min_L1_b; cout << endl;
        vec<Formula*> sum;
        
        for (int j = 0; j < n; j++)
            sum.push(NULL);
        
        Formula* tmp1, *tmp2, *carry, *sum_neg, *carry_neg, *add_neg;
        
        sum[0] = new Formula(*formuli[0]);
        for (int j = 1; j < formuli.size(); j++)
        {
            sum_neg = new Formula(*sum[0]); sum_neg->negate();
            add_neg = new Formula(*formuli[j]); add_neg->negate();
            
            tmp1 = new Formula();
            tmp1->add(sum[0]);
            tmp1->add(add_neg);
            
            tmp2 = new Formula();
            tmp2->add(sum_neg);
            tmp2->add(formuli[j]);
            
            carry = new Formula();
            carry->add(sum[0]);
            carry->add(formuli[j]);
            
            sum[0] = new Formula(F_OR);
            sum[0]->add(tmp1);
            sum[0]->add(tmp2);
            
            int k;
            for (k = 1; sum[k]!=NULL && k < sum.size(); k++)
            {
                carry_neg = new Formula(*carry);
                sum_neg = new Formula(* (Formula*) sum[k]);
                
                sum_neg->negate(); carry_neg->negate();
                
                tmp1 = new Formula();
                tmp1->add(sum[k]);
                tmp1->add(carry_neg);
                
                tmp2 = new Formula();
                tmp2->add(sum_neg);
                tmp2->add(carry);
                
                tmp3 = new Formula();
                tmp3->add(sum[k]);
                tmp3->add(carry);
                
                sum[k] = new Formula(F_OR);
                sum[k]->add(tmp1);
                sum[k]->add(tmp2);
                
                carry = tmp3;
                
            }
            if (k < sum.size()) sum[k] = carry;
        }
        
        
        k_secure->add(geq(sum, min_L1_b, 0));
        //		cout << "end of loop" << endl;
    }
    
    sat->add(k_secure);
    cout << sat->maxVar();
    //	cout << sat->str();
    
    Formula cnf_sat;
    Lit out;
    Solver mySolver;
    sat->export_cnf(out, NULL, &mySolver);
    sat->export_cnf(out, &cnf_sat, NULL);
    cnf_sat.add(out);
    
    mySolver.addClause(out);
    //	cout << endl << cnf_sat.maxVar();
    //	mySolver.solve();
    cout << endl << "done";
    //	cout.flush();
    
    if (!mySolver.solve()) cout << endl << "Problem is not in LIFT" << endl;
    else
    {
        for (int i=0; i<igraph_ecount(G); i++)
            
            if (mySolver.modelValue(e(i+1)) != l_False) { Edge edge; igraph_edge(G, i, &edge.first, &edge.second); self->H->del_edge(edge); }
        //		for (int j=0; j < igraph_vector_ptr_size(&match_vert); j++)
        //		{
        //			cout << j << " ";
        //			igraph_vector_t* v = (igraph_vector_t*) VECTOR(match_vert)[j];
        //			for (int k=0; k < igraph_vector_size(v); k++) cout << VECTOR(*v)[k] << " ";
        //			cout << endl;
        //		}
        //		for (int j=0; j < mySolver.model.size(); j++)
        //			cout << (mySolver.model[j]==l_False? "false" : "true") << " ";
        for (int j=0; j < igraph_vcount(G); j++)
        {
            for (int k=0; k < igraph_vcount(G); k++)
            {
                cout << j << "->" << k << ": " << (mySolver.modelValue(phi(10,1,j,k))==l_False? "false": "true"); cout << " ";
            }
            cout << endl;
        }
    }
    
    cout << "ecount_less_than_eta is: " << (ecount_less_than_eta->evaluate(&mySolver)? "True" : "False") << endl;
    cout << "k_secure is: " << (k_secure->evaluate(&mySolver)? "True" : "False") << endl;
    cout << "sat is: " << (sat->evaluate(&mySolver)? "True" : "False") << endl;
    cout << "cnf_sat is: " << (cnf_sat.evaluate(&mySolver)? "True" : "False") << endl;
    cout.flush();
    //	Grabage Collection
    for (int i =0; i < igraph_vector_ptr_size(&match_vert); i++)
        igraph_vector_destroy((igraph_vector_t*) VECTOR(match_vert)[i]);
    igraph_vector_ptr_destroy(&match_vert);
    
    //	for (int i = 0; i < sum.size(); i++) delete sum[i];
    
    //	delete carry, tmp1, tmp2, tmp3, carry_neg, sum_neg, sat;
    //	delete sat;
}

int Security::rSAT(int min_L1, int max_L1, int eta) { return C_SAT(this, min_L1, max_L1, eta); };

int Security::rSAT(int min_L1, int max_L1, int eta, int u, bool quite) { return C_SAT(this, min_L1, max_L1, eta, u, quite); };

int Security::rSAT(int min_L1, int max_L1, int eta, int u) { return C_SAT(this, min_L1, max_L1, eta, u); };

C_SAT::C_SAT(Security* security, int min_L1, int max_L1, int eta, int u, bool quite) {
    
    self = security;
    Circuit* G = self->G;
    sat = new Formula(F_AND);
    igraph_vector_ptr_init(&match_vert, 0);
    for (int i = 0; i < igraph_vcount(G); i++)
    {
        int color = VAN(G, "colour", i);
        if (igraph_vector_ptr_size(&match_vert) < color + 1)
            for (int j = igraph_vector_ptr_size(&match_vert); j <= color; j++)
            {
                igraph_vector_t* v = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                igraph_vector_init(v, 0);
                igraph_vector_ptr_push_back(&match_vert, v);
            }
        igraph_vector_push_back((igraph_vector_t*) VECTOR(match_vert)[color], i);
    }
    
    for (int i=0; i < igraph_vector_ptr_size(&match_vert); i++)
    {
        for (int j=0; j < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[i]); j++)
            cout << igraph_vector_e((igraph_vector_t*) VECTOR(match_vert)[i], j) << "";
        cout << endl;
    }
    
    cout.flush();
    
    //	int nVars
    
    for (int i=0; i < igraph_vector_ptr_size(&match_vert); i++)
    {
        int n = igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[i]);
        for (int j=0; j < n * n * (igraph_vcount(G))*(igraph_vcount(G)); j++)
            sat->newVar();
    }
    
    for (int i=0; i < igraph_ecount(G); i++) sat->newVar();
    marker = sat->maxVar();
    int n = (int) floor(log(igraph_ecount(G))/log(2)+1);
    //	char* eta_b = (char*) malloc(n);
    
    string eta_b = convertInt(eta);
    string temp="";
    for (int i = eta_b.length(); i < n; i++)
        temp+='0';
    
    eta_b=temp+eta_b;
    vec<Formula*> sum;
    
    for (int i = 0; i < n; i++)
        sum.push(NULL);
    
    Formula* tmp1 = new Formula(), *tmp2 = new Formula(), *tmp3 = new Formula(), *carry = new Formula(), *sum_neg = new Formula(), *carry_neg = new Formula();
    tmp1->add(mkLit(e(1)));
    tmp1->add(mkLit(e(2), true));
    
    tmp2->add(mkLit(e(1), true));
    tmp2->add(mkLit(e(2)));
    
    sum[0] = new Formula(F_OR);
    sum[0]->add(tmp1);
    sum[0]->add(tmp2);
    
    carry->add(mkLit(e(1)));
    carry->add(mkLit(e(2)));
    
    sum[1] = carry;
    
    for (int i = 3; i <= igraph_ecount(G); i++)
    {
        sum_neg = new Formula(*sum[0]); sum_neg->negate();
        tmp1 = new Formula();
        tmp1->add(sum[0]);
        tmp1->add(mkLit(e(i), true));
        
        tmp2 = new Formula();
        tmp2->add(sum_neg);
        tmp2->add(mkLit(e(i)));
        
        carry = new Formula();
        carry->add(sum[0]);
        carry->add(mkLit(e(i)));
        
        sum[0] = new Formula(F_OR);
        sum[0]->add(tmp1);
        sum[0]->add(tmp2);
        
        int j;
        for (j = 1; sum[j]!=NULL && j < sum.size(); j++)
        {
            Formula* carry_neg = new Formula(*carry);
            sum_neg = new Formula(*sum[j]);
            
            sum_neg->negate(); carry_neg->negate();
            
            tmp1 = new Formula();
            tmp1->add(sum[j]);
            tmp1->add(carry_neg);
            
            tmp2 = new Formula();
            tmp2->add(sum_neg);
            tmp2->add(carry);
            
            tmp3 = new Formula();
            tmp3->add(sum[j]);
            tmp3->add(carry);
            
            sum[j] = new Formula(F_OR);
            sum[j]->add(tmp1);
            sum[j]->add(tmp2);
            
            carry = tmp3;
            
        }
        if (j < sum.size()) sum[j] = carry;
    }
    
    
    Formula* ecount_less_than_eta = leq(sum, eta_b, 0);
    //cout << ecount_less_than_eta->str();
    sat->add(ecount_less_than_eta);
    
    Formula* k_secure = new Formula(F_AND);
    
    
    //	vec<Formula*> formuli;
    
    int i = u;
    //	for (int i = 0; i < igraph_vcount(G); i++)
    {
        int color = VAN(G, "colour", i);
        vec<Formula*> formuli;
        for (int j1 = 0; j1 < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[color]); j1++)
        {
            int j = igraph_vector_e((igraph_vector_t*) VECTOR(match_vert)[color], j1);
            Formula* F1 = new Formula(F_AND);
            for (int k = 0; k < igraph_vcount(G); k++)
            {	if (k == i) continue;
                int k_color = VAN(G, "colour", k);
                Formula* nested = new Formula(F_OR);
                //				for (int l = 0; l < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); l++)
                for (int l = 0; l < igraph_vcount(G); l++)
                {	if (l == j) continue;
                    Formula* nested1 = new Formula(F_AND);
                    int l_color = VAN(G, "colour", l);
                    if (k_color != l_color) continue;
                    if (k == i && l != j) continue;
                    if (k != i || l != j) nested1->add(mkLit(phi(i, j, k, l)));
                    
                    for (int h = 0; h < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); h++)
                        //					for (int h = 0; h < igraph_vcount(G); h++)
                    {
                        igraph_vector_t *vec = (igraph_vector_t *) VECTOR(match_vert)[k_color];
                        if (VECTOR(*vec)[h] != l && VECTOR(*vec)[h] != j) nested1->add(mkLit(phi(i, j, k, VECTOR(*vec)[h]), true));
                    }
                    nested->add(nested1);
                }
                F1->add(nested);
            }
            
            Formula* F2 = new Formula(F_AND);
            for (int k = 0; k < igraph_vcount(G); k++)
            {	if (k==j) continue;
                int k_color = VAN(G, "colour", k);
                Formula* nested = new Formula(F_OR);
                //for (int l = 0; l < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); l++)
                for (int l = 0; l < igraph_vcount(G); l++)
                {	if (l==i) continue;
                    Formula* nested1 = new Formula(F_AND);
                    int l_color = VAN(G, "colour", l);
                    if (k_color != l_color) continue;
                    if (k == j && l != i) continue;
                    if (k != j || l != i) nested1->add(mkLit(phi(i, j, l, k)));
                    
                    for (int h = 0; h < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); h++)
                    {
                        //					for (int h = 0; h < igraph_vcount(G); h++)
                        igraph_vector_t *vec = (igraph_vector_t *) VECTOR(match_vert)[k_color];
                        if (VECTOR(*vec)[h] != l && VECTOR(*vec)[h] != i) nested1->add(mkLit(phi(i, j, VECTOR(*vec)[h], k), true));
                    }
                    nested->add(nested1);
                }
                F2->add(nested);
            }
            
            Formula* F3 = new Formula(F_AND);
            for (int k = 0; k < igraph_ecount(G); k++)
            {
                //				F3->add(mkLit(e(k),true));
                Formula* nested = new Formula(F_OR);
                nested->add(mkLit(e(k+1)));
                for (int l = 0; l < igraph_ecount(G); l++)
                {
                    int src_l, dest_l, src_k, dest_k;
                    igraph_edge(G, l, &src_l, &dest_l);
                    int src_col_k, dest_col_k, src_col_l, dest_col_l;
                    src_col_l = VAN(G, "colour", src_l);
                    dest_col_l = VAN(G, "colour", dest_l);
                    //					if (src_col != dest_col) continue;
                    igraph_edge(G, k, &src_k, &dest_k);
                    src_col_k = VAN(G, "colour", src_k);
                    dest_col_k = VAN(G, "colour", dest_k);
                    if (src_col_l != src_col_k || dest_col_l != dest_col_k) continue;
                    //					if (src_k == i && src_l == j && dest_k == i && dest_l == j) break;
                    if (src_k == i && src_l != j || dest_k == i && dest_l != j) continue;
                    if (src_k != i && src_l == j || dest_k != i && dest_l == j) continue;
                    if (src_k == i && src_l == j) { nested->add(mkLit(phi(i,j,dest_k,dest_l))); continue; }
                    if (dest_k == i && dest_l == j) { nested->add(mkLit(phi(i,j,src_k,src_l))); continue; }
                    Formula* p = new Formula(F_AND);
                    p->add(mkLit(phi(i,j,src_k,src_l)));
                    p->add(mkLit(phi(i,j,dest_k,dest_l)));
                    nested->add(p);
                }
                F3->add(nested);
            }
            
            Formula* F = new Formula(F_AND);
            F->add(F1);
            F->add(F2);
            F->add(F3);
            formuli.push(F);
            if (i == 10 && j == 1) cout << F->str();
        }
        
        int n = (int) floor(log(igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[color]))/log(2)+1);
        //		char* min_L1_b = (char*) malloc(n);
        
        string min_L1_b = convertInt(min_L1);
        
        string temp="";
        for (int j = min_L1_b.length(); j < n; j++)
            temp+="0";
        min_L1_b=temp+min_L1_b;
        cout << min_L1_b; cout << endl;
        vec<Formula*> sum;
        
        for (int j = 0; j < n; j++)
            sum.push(NULL);
        
        Formula* tmp1, *tmp2, *carry, *sum_neg, *carry_neg, *add_neg;
        
        sum[0] = new Formula(*formuli[0]);
        for (int j = 1; j < formuli.size(); j++)
        {
            sum_neg = new Formula(*sum[0]); sum_neg->negate();
            add_neg = new Formula(*formuli[j]); add_neg->negate();
            
            tmp1 = new Formula();
            tmp1->add(sum[0]);
            tmp1->add(add_neg);
            
            tmp2 = new Formula();
            tmp2->add(sum_neg);
            tmp2->add(formuli[j]);
            
            carry = new Formula();
            carry->add(sum[0]);
            carry->add(formuli[j]);
            
            sum[0] = new Formula(F_OR);
            sum[0]->add(tmp1);
            sum[0]->add(tmp2);
            
            int k;
            for (k = 1; sum[k]!=NULL && k < sum.size(); k++)
            {
                carry_neg = new Formula(*carry);
                sum_neg = new Formula(* (Formula*) sum[k]);
                
                sum_neg->negate(); carry_neg->negate();
                
                tmp1 = new Formula();
                tmp1->add(sum[k]);
                tmp1->add(carry_neg);
                
                tmp2 = new Formula();
                tmp2->add(sum_neg);
                tmp2->add(carry);
                
                tmp3 = new Formula();
                tmp3->add(sum[k]);
                tmp3->add(carry);
                
                sum[k] = new Formula(F_OR);
                sum[k]->add(tmp1);
                sum[k]->add(tmp2);
                
                carry = tmp3;
                
            }
            if (k < sum.size()) sum[k] = carry;
        }
        
        
        k_secure->add(geq(sum, min_L1_b, 0));
        //		cout << "end of loop" << endl;
    }
    
    sat->add(k_secure);
    cout << sat->maxVar();
    //	cout << sat->str();
    
    Formula cnf_sat;
    Lit out;
    Solver mySolver;
    sat->export_cnf(out, NULL, &mySolver);
    sat->export_cnf(out, &cnf_sat, NULL);
    cnf_sat.add(out);
    
    mySolver.addClause(out);
    //	cout << endl << cnf_sat.maxVar();
    //	mySolver.solve();
    cout << endl << "done";
    //	cout.flush();
    
    if (!mySolver.solve()) cout << endl << "Problem is not in LIFT" << endl;
    else
    {
        for (int i=0; i<igraph_ecount(G); i++)
            
            if (mySolver.modelValue(e(i+1)) != l_False) { Edge edge; igraph_edge(G, i, &edge.first, &edge.second); self->H->del_edge(edge); }
        //		for (int j=0; j < igraph_vector_ptr_size(&match_vert); j++)
        //		{
        //			cout << j << " ";
        //			igraph_vector_t* v = (igraph_vector_t*) VECTOR(match_vert)[j];
        //			for (int k=0; k < igraph_vector_size(v); k++) cout << VECTOR(*v)[k] << " ";
        //			cout << endl;
        //		}
        //		for (int j=0; j < mySolver.model.size(); j++)
        //			cout << (mySolver.model[j]==l_False? "false" : "true") << " ";
        for (int j=0; j < igraph_vcount(G); j++)
        {
            for (int k=0; k < igraph_vcount(G); k++)
            {
                cout << j << "->" << k << ": " << (mySolver.modelValue(phi(10,1,j,k))==l_False? "false": "true"); cout << " ";
            }
            cout << endl;
        }
    }
    
    cout << "ecount_less_than_eta is: " << (ecount_less_than_eta->evaluate(&mySolver)? "True" : "False") << endl;
    cout << "k_secure is: " << (k_secure->evaluate(&mySolver)? "True" : "False") << endl;
    cout << "sat is: " << (sat->evaluate(&mySolver)? "True" : "False") << endl;
    cout << "cnf_sat is: " << (cnf_sat.evaluate(&mySolver)? "True" : "False") << endl;
    cout.flush();
    //	Grabage Collection
    for (int i =0; i < igraph_vector_ptr_size(&match_vert); i++)
        igraph_vector_destroy((igraph_vector_t*) VECTOR(match_vert)[i]);
    igraph_vector_ptr_destroy(&match_vert);
    
    //	for (int i = 0; i < sum.size(); i++) delete sum[i];
    
    //	delete carry, tmp1, tmp2, tmp3, carry_neg, sum_neg, sat;
    //	delete sat;
}

C_SAT::C_SAT(Security* security, int min_L1, int max_L1, int eta, int u) {
    
    self = security;
    Circuit* G = self->G;
    sat = new Formula(F_AND);
    igraph_vector_ptr_init(&match_vert, 0);
    for (int i = 0; i < igraph_vcount(G); i++)
    {
        int color = VAN(G, "colour", i);
        if (igraph_vector_ptr_size(&match_vert) < color + 1)
            for (int j = igraph_vector_ptr_size(&match_vert); j <= color; j++)
            {
                igraph_vector_t* v = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                igraph_vector_init(v, 0);
                igraph_vector_ptr_push_back(&match_vert, v);
            }
        igraph_vector_push_back((igraph_vector_t*) VECTOR(match_vert)[color], i);
    }
    
    for (int i=0; i < igraph_vector_ptr_size(&match_vert); i++)
    {
        for (int j=0; j < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[i]); j++)
            cout << igraph_vector_e((igraph_vector_t*) VECTOR(match_vert)[i], j) << "";
        cout << endl;
    }
    
    cout.flush();
    
    //	int nVars
    
    for (int i=0; i < igraph_vector_ptr_size(&match_vert); i++)
    {
        int n = igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[i]);
        for (int j=0; j < n * n * (igraph_vcount(G))*(igraph_vcount(G)); j++)
            sat->newVar();
    }
    
    for (int i=0; i < igraph_ecount(G); i++) sat->newVar();
    
    marker = sat->maxVar();
    
    int n = (int) floor(log(igraph_ecount(G))/log(2)+1);
    //	char* eta_b = (char*) malloc(n);
    
    vec<Formula*> sum;
    vec<Var> sum_var;
    
    for (int i = 0; i < n; i++)
    { sum.push(NULL); sum_var.push(0); }
    
    Formula* tmp1 = new Formula(), *tmp2 = new Formula(), *tmp3 = new Formula(F_OR), *carry = new Formula(), *sum_neg, *carry_neg;
    tmp1->add(mkLit(e(1)));
    tmp1->add(mkLit(e(2), true));
    
    tmp2->add(mkLit(e(1), true));
    tmp2->add(mkLit(e(2)));
    
    sum_var[0] = sat->newVar();
    sum[0] = new Formula(F_OR);
    sum[0]->add(tmp1);
    sum[0]->add(tmp2);
    sum_neg = new Formula(*sum[0]);
    sum_neg->negate();
    Formula* tmp4 = new Formula();
    tmp4->add(mkLit(sum_var[0]));
    tmp4->add(sum[0]);
    
    tmp3->add(tmp4);
    tmp4 = new Formula();
    tmp4->add(mkLit(sum_var[0], true));
    tmp4->add(sum_neg);
    tmp3->add(tmp4);
    
    sum[0]=new Formula();
    sat->add(tmp3); //sum[0]->add(tmp3);
    
    carry->add(mkLit(e(1)));
    carry->add(mkLit(e(2)));
    carry_neg = new Formula(*carry);
    carry_neg->negate();
    int carry_var = sat->newVar();
    tmp3 = new Formula(F_OR);
    tmp4 = new Formula();
    tmp4->add(mkLit(carry_var));
    tmp4->add(carry);
    
    tmp3->add(tmp4);
    tmp4 = new Formula();
    tmp4->add(mkLit(carry_var, true));
    tmp4->add(carry_neg);
    tmp3->add(tmp4);
    
    sum[1] = new Formula();
    sat->add(tmp3); // sum[1]->add(tmp3);
    sum_var[1] = carry_var;
    
    //cout << "Before loop: " << sum[1]->maxVar() << endl;
    for (int i = 3; i <= igraph_ecount(G); i++)
    {
        Lit sum_neg = mkLit(sum_var[0], true); //sum_neg->negate();
        tmp1 = new Formula();
        tmp1->add(mkLit(sum_var[0]));
        tmp1->add(mkLit(e(i), true));
        
        tmp2 = new Formula();
        tmp2->add(sum_neg);
        tmp2->add(mkLit(e(i)));
        
        carry = new Formula();
        carry->add(mkLit(sum_var[0]));
        carry->add(mkLit(e(i)));
        
        sum_var[0] = sat->newVar();
        Formula* tmp5 = new Formula(F_OR);
        tmp5->add(tmp1);
        tmp5->add(tmp2);
        
        tmp3 = new Formula(); tmp4 = new Formula(F_OR);
        Formula* tmp5_neg = new Formula(*tmp5); tmp5_neg->negate();
        tmp3->add(mkLit(sum_var[0])); tmp3->add(tmp5);
        tmp4->add(tmp3);
        tmp3 = new Formula();
        tmp3->add(mkLit(sum_var[0], true)); tmp3->add(tmp5_neg);
        tmp4->add(tmp3);
        
        sat->add(tmp4); //sum[0]->add(tmp4);
        
        int carry_var = sat->newVar();
        carry_neg = new Formula(*carry); carry_neg->negate();
        tmp3 = new Formula(); //tmp4 = new Formula(F_OR);
        tmp3->add(mkLit(carry_var)); tmp3->add(carry);
        carry = new Formula(F_OR); carry->add(tmp3);
        tmp3 = new Formula();
        tmp3->add(mkLit(carry_var, true)); tmp3->add(carry_neg);
        carry->add(tmp3);
        //		sum[1]->add(carry);
        
        int j;
        for (j = 1; sum[j]!=NULL && j < sum.size(); j++)
        {
            //		cout << sum[j]->maxVar() << endl;
            sat->add(carry);
            // sum[j]->add(carry);
            
            //		cout << sum[j]->maxVar() << " " << carry->maxVar() << endl;
            // Formula* carry_neg = new Formula(*carry);
            Lit carry_neg = mkLit(carry_var, true);
            Lit sum_neg = mkLit(sum_var[j], true); //new Formula(*sum[j]);
            
            //			sum_neg->negate(); carry_neg->negate();
            
            tmp1 = new Formula();
            tmp1->add(mkLit(sum_var[j]));
            tmp1->add(carry_neg);
            
            tmp2 = new Formula();
            tmp2->add(sum_neg);
            tmp2->add(mkLit(carry_var));
            
            tmp3 = new Formula();
            tmp3->add(mkLit(sum_var[j]));
            tmp3->add(mkLit(carry_var));
            
            
            tmp4 = new Formula(F_OR);
            tmp4->add(tmp1);
            tmp4->add(tmp2);
            
            sum_var[j] = sat->newVar();
            
            Formula* tmp4_neg = new Formula(*tmp4); tmp4_neg->negate();
            Formula* tmp5 = new Formula(), *tmp6 = new Formula(F_OR);
            
            //		cout << "tmp4: " << tmp4->maxVar() << endl;
            //			cout << "sum_var[j]: " << mkLit(sum_var[j]) << endl;
            tmp5->add(mkLit(sum_var[j])); tmp5->add(tmp4);
            tmp6->add(tmp5);
            tmp5 = new Formula();
            tmp5->add(mkLit(sum_var[j], true)); tmp5->add(tmp4_neg);
            
            //			cout << "tmp5: " << tmp5->maxVar() << endl;
            tmp6->add(tmp5);
            
            //			cout << "tmp6: " << tmp6->maxVar() << endl;
            // sum[j]->add(tmp6);
            sat->add(tmp6);
            
            carry_var = sat->newVar();
            Formula* tmp3_neg = new Formula(*tmp3); tmp3_neg->negate();
            tmp4 = new Formula(); tmp4->add(mkLit(carry_var)); tmp4->add(tmp3);
            carry = new Formula(F_OR); carry->add(tmp4);
            tmp4 = new Formula(); tmp4->add(mkLit(carry_var, true)); tmp4->add(tmp3_neg);
            carry->add(tmp4);
            
            //		cout << "End loop body: " << sum[j]->maxVar() << endl;
        }
        if (j < sum.size()) { sum[j] = new Formula(); sat->add(carry); sum_var[j] = carry_var; }
    }
    
    //	cout << endl << ecount_less_than_eta->str();
    //	cout << endl << leqf->str();
    
    //	sat->add(ecount_less_than_eta);
    
    Formula* k_secure = new Formula(F_AND);
    
    vec<Formula*> formuli;
    
    int i = u;
    
    //	for (int i = 0; i < igraph_vcount(G); i++)
    {
        int color = VAN(G, "colour", i);
        //		vec<Formula*> formuli;
        //		Formula* formula1 = new Formula(F_OR);
        for (int j1 = 0; j1 < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[color]); j1++)
        {
            int j = igraph_vector_e((igraph_vector_t*) VECTOR(match_vert)[color], j1);
            if (j == i) continue;
            Formula* F1 = new Formula(F_AND);
            for (int k = 0; k < igraph_vcount(G); k++)
            {	if (k == i) continue;
                int k_color = VAN(G, "colour", k);
                Formula* nested = new Formula(F_OR);
                //				for (int l = 0; l < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); l++)
                for (int l = 0; l < igraph_vcount(G); l++)
                {	if (l == j) continue;
                    Formula* nested1 = new Formula(F_AND);
                    int l_color = VAN(G, "colour", l);
                    if (k_color != l_color) continue;
                    if (k == i && l != j) continue;
                    if (k != i || l != j) nested1->add(mkLit(phi(i, j, k, l)));
                    
                    for (int h = 0; h < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); h++)
                        //					for (int h = 0; h < igraph_vcount(G); h++)
                    {
                        igraph_vector_t *vec = (igraph_vector_t *) VECTOR(match_vert)[k_color];
                        if (VECTOR(*vec)[h] != l && VECTOR(*vec)[h] != j) nested1->add(mkLit(phi(i, j, k, VECTOR(*vec)[h]), true));
                    }
                    nested->add(nested1);
                }
                F1->add(nested);
            }
            
            Formula* F2 = new Formula(F_AND);
            for (int k = 0; k < igraph_vcount(G); k++)
            {	if (k==j) continue;
                int k_color = VAN(G, "colour", k);
                Formula* nested = new Formula(F_OR);
                //for (int l = 0; l < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); l++)
                for (int l = 0; l < igraph_vcount(G); l++)
                {	if (l==i) continue;
                    Formula* nested1 = new Formula(F_AND);
                    int l_color = VAN(G, "colour", l);
                    if (k_color != l_color) continue;
                    if (k == j && l != i) continue;
                    if (k != j || l != i) nested1->add(mkLit(phi(i, j, l, k)));
                    
                    for (int h = 0; h < igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[k_color]); h++)
                    {
                        //					for (int h = 0; h < igraph_vcount(G); h++)
                        igraph_vector_t *vec = (igraph_vector_t *) VECTOR(match_vert)[k_color];
                        if (VECTOR(*vec)[h] != l && VECTOR(*vec)[h] != i) nested1->add(mkLit(phi(i, j, VECTOR(*vec)[h], k), true));
                    }
                    nested->add(nested1);
                }
                F2->add(nested);
            }
            
            Formula* F3 = new Formula(F_AND);
            for (int k = 0; k < igraph_ecount(G); k++)
            {
                Formula* nested = new Formula(F_OR);
                nested->add(mkLit(e(k+1)));
                for (int l = 0; l < igraph_ecount(G); l++)
                {
                    int src_l, dest_l, src_k, dest_k;
                    igraph_edge(G, l, &src_l, &dest_l);
                    int src_col_k, dest_col_k, src_col_l, dest_col_l;
                    src_col_l = VAN(G, "colour", src_l);
                    dest_col_l = VAN(G, "colour", dest_l);
                    igraph_edge(G, k, &src_k, &dest_k);
                    src_col_k = VAN(G, "colour", src_k);
                    dest_col_k = VAN(G, "colour", dest_k);
                    if (src_col_l != src_col_k || dest_col_l != dest_col_k) continue;
                    if (src_k == i && src_l != j || dest_k == i && dest_l != j) continue;
                    if (src_k != i && src_l == j || dest_k != i && dest_l == j) continue;
                    if (src_k == i && src_l == j) { nested->add(mkLit(phi(i,j,dest_k,dest_l))); continue; }
                    if (dest_k == i && dest_l == j) { nested->add(mkLit(phi(i,j,src_k,src_l))); continue; }
                    Formula* p = new Formula(F_AND);
                    p->add(mkLit(phi(i,j,src_k,src_l)));
                    p->add(mkLit(phi(i,j,dest_k,dest_l)));
                    nested->add(p);
                }
                F3->add(nested);
            }
            
            Formula* F = new Formula(F_AND);
            F->add(F1);
            F->add(F2);
            F->add(F3);
            //			formula1->add(F);
            formuli.push(F);
        }
        //		k_secure->add(formula1);
    }
    
    {
        igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[(int) VAN(G, "colour", i)]);
        int n1 = (int) floor(log(	igraph_vector_size((igraph_vector_t*) VECTOR(match_vert)[(int) VAN(G, "colour", i)])-1)/log(2)+1);
        //	char* eta_b = (char*) malloc(n);
        
        vec<Formula*> sum;
        //	sum.clear();
        vec<Var> sum_var;
        //	sum_var.clear();
        
        for (int i = 0; i < n1; i++)
        { sum.push(NULL); sum_var.push(0); }
        
        
        Formula* tmp1 = new Formula(), *tmp2 = new Formula(), *tmp3 = new Formula(F_OR), *carry = new Formula(), *sum_neg, *carry_neg;
        tmp1->add(formuli[0]);
        Formula* formula1_neg = new Formula(*formuli[1]); formula1_neg->negate();
        tmp1->add(formula1_neg);
        
        Formula* formula0_neg = new Formula(*formuli[0]); formula0_neg->negate();
        tmp2->add(formula0_neg);
        tmp2->add(formuli[1]);
        
        sum_var[0] = sat->newVar();
        sum[0] = new Formula(F_OR);
        sum[0]->add(tmp1);
        sum[0]->add(tmp2);
        sum_neg = new Formula(*sum[0]);
        sum_neg->negate();
        Formula* tmp4 = new Formula();
        tmp4->add(mkLit(sum_var[0]));
        tmp4->add(sum[0]);
        
        tmp3->add(tmp4);
        tmp4 = new Formula();
        tmp4->add(mkLit(sum_var[0], true));
        tmp4->add(sum_neg);
        tmp3->add(tmp4);
        
        sum[0]=new Formula();
        sat->add(tmp3); //sum[0]->add(tmp3);
        
        carry->add(formuli[0]);
        carry->add(formuli[1]);
        carry_neg = new Formula(*carry);
        carry_neg->negate();
        int carry_var = sat->newVar();
        tmp3 = new Formula(F_OR);
        tmp4 = new Formula();
        tmp4->add(mkLit(carry_var));
        tmp4->add(carry);
        
        tmp3->add(tmp4);
        tmp4 = new Formula();
        tmp4->add(mkLit(carry_var, true));
        tmp4->add(carry_neg);
        tmp3->add(tmp4);
        
        sum[1] = new Formula();
        sat->add(tmp3); // sum[1]->add(tmp3);
        sum_var[1] = carry_var;
        
        //cout << "Before loop: " << sum[1]->maxVar() << endl;
        for (int i = 2; i < formuli.size(); i++)
        {
            Lit sum_neg = mkLit(sum_var[0], true); //sum_neg->negate();
            tmp1 = new Formula();
            tmp1->add(mkLit(sum_var[0]));
            Formula* formulii_neg = new Formula(*formuli[i]); formulii_neg->negate();
            tmp1->add(formulii_neg);
            
            tmp2 = new Formula();
            tmp2->add(sum_neg);
            tmp2->add(formuli[i]);
            
            carry = new Formula();
            carry->add(mkLit(sum_var[0]));
            carry->add(formuli[i]);
            
            sum_var[0] = sat->newVar();
            Formula* tmp5 = new Formula(F_OR);
            tmp5->add(tmp1);
            tmp5->add(tmp2);
            
            tmp3 = new Formula(); tmp4 = new Formula(F_OR);
            Formula* tmp5_neg = new Formula(*tmp5); tmp5_neg->negate();
            tmp3->add(mkLit(sum_var[0])); tmp3->add(tmp5);
            tmp4->add(tmp3);
            tmp3 = new Formula();
            tmp3->add(mkLit(sum_var[0], true)); tmp3->add(tmp5_neg);
            tmp4->add(tmp3);
            
            sat->add(tmp4); //sum[0]->add(tmp4);
            
            int carry_var = sat->newVar();
            carry_neg = new Formula(*carry); carry_neg->negate();
            tmp3 = new Formula(); //tmp4 = new Formula(F_OR);
            tmp3->add(mkLit(carry_var)); tmp3->add(carry);
            carry = new Formula(F_OR); carry->add(tmp3);
            tmp3 = new Formula();
            tmp3->add(mkLit(carry_var, true)); tmp3->add(carry_neg);
            carry->add(tmp3);
            //		sum[1]->add(carry);
            
            int j;
            for (j = 1; sum[j]!=NULL && j < sum.size(); j++)
            {
                //		cout << sum[j]->maxVar() << endl;
                sat->add(carry);
                // sum[j]->add(carry);
                
                //		cout << sum[j]->maxVar() << " " << carry->maxVar() << endl;
                // Formula* carry_neg = new Formula(*carry);
                Lit carry_neg = mkLit(carry_var, true);
                Lit sum_neg = mkLit(sum_var[j], true); //new Formula(*sum[j]);
                
                //			sum_neg->negate(); carry_neg->negate();
                
                tmp1 = new Formula();
                tmp1->add(mkLit(sum_var[j]));
                tmp1->add(carry_neg);
                
                tmp2 = new Formula();
                tmp2->add(sum_neg);
                tmp2->add(mkLit(carry_var));
                
                tmp3 = new Formula();
                tmp3->add(mkLit(sum_var[j]));
                tmp3->add(mkLit(carry_var));
                
                
                tmp4 = new Formula(F_OR);
                tmp4->add(tmp1);
                tmp4->add(tmp2);
                
                sum_var[j] = sat->newVar();
                
                Formula* tmp4_neg = new Formula(*tmp4); tmp4_neg->negate();
                Formula* tmp5 = new Formula(), *tmp6 = new Formula(F_OR);
                
                //		cout << "tmp4: " << tmp4->maxVar() << endl;
                //			cout << "sum_var[j]: " << mkLit(sum_var[j]) << endl;
                tmp5->add(mkLit(sum_var[j])); tmp5->add(tmp4);
                tmp6->add(tmp5);
                tmp5 = new Formula();
                tmp5->add(mkLit(sum_var[j], true)); tmp5->add(tmp4_neg);
                
                //			cout << "tmp5: " << tmp5->maxVar() << endl;
                tmp6->add(tmp5);
                
                //			cout << "tmp6: " << tmp6->maxVar() << endl;
                // sum[j]->add(tmp6);
                sat->add(tmp6);
                
                carry_var = sat->newVar();
                Formula* tmp3_neg = new Formula(*tmp3); tmp3_neg->negate();
                tmp4 = new Formula(); tmp4->add(mkLit(carry_var)); tmp4->add(tmp3);
                carry = new Formula(F_OR); carry->add(tmp4);
                tmp4 = new Formula(); tmp4->add(mkLit(carry_var, true)); tmp4->add(tmp3_neg);
                carry->add(tmp4);
                
                //		cout << "End loop body: " << sum[j]->maxVar() << endl;
            }
            if (j < sum.size()) { sum[j] = new Formula(); sat->add(carry); sum_var[j] = carry_var; }
        }
        
        string min_L1_b = convertInt(min_L1-1);
        string temp="";
        for (int i = min_L1_b.length(); i < n1; i++)
            temp+='0';
        
        min_L1_b=temp+min_L1_b;
        
        Formula* geqf = geq(sum_var,min_L1_b,0);
        Formula* geqf_neg = new Formula(*geqf); geqf_neg->negate();
        
        Var comp_var = sat->newVar();
        Formula* temp1 = new Formula(F_OR), * temp2 = new Formula();
        temp2->add(geqf); temp2->add(mkLit(comp_var));
        temp1->add(temp2); temp2 = new Formula();
        temp2->add(geqf_neg); temp2->add(mkLit(comp_var,true));
        temp1->add(temp2);
        
        
        sat->add(mkLit(comp_var)); sat->add(temp1);
        
    }
    
    
    //	sat->add(k_secure);
    
    int upper = igraph_ecount(G), lower = 0;
    vec<lbool> solution;
    
    while (upper > lower + 1)
    {
        int eta = (upper + lower) / 2;
        string eta_b = convertInt(eta);
        string temp="";
        for (int i = eta_b.length(); i < n; i++)
            temp+='0';
        
        eta_b=temp+eta_b;
        
        Formula* leqf = leq(sum_var,eta_b,0);
        Formula* leqf_neg = new Formula(*leqf); leqf_neg->negate();
        
        Formula* final_sat = new Formula(); final_sat->add(sat);
        Var comp_var = final_sat->newVar();
        Formula* temp1 = new Formula(F_OR), * temp2 = new Formula();
        temp2->add(leqf); temp2->add(mkLit(comp_var));
        temp1->add(temp2); temp2 = new Formula();
        temp2->add(leqf_neg); temp2->add(mkLit(comp_var,true));
        temp1->add(temp2);
        
        
        final_sat->add(mkLit(comp_var)); final_sat->add(temp1);
        
        Lit out;
        Solver mySolver;
        cout << "here..." << endl;
        final_sat->export_cnf(out, NULL, &mySolver);
        cout << "done";
        mySolver.addClause(out);
        delete temp1;
        
        //delete sat;
        cout << endl << "done";
        
        if (!mySolver.solve()) { lower = eta; cout << endl << "Problem is not in LIFT for eta = " << eta << endl; }
        else
        {
            upper = eta;
            mySolver.model.copyTo(solution);
            cout << endl << "Problem is in LIFT for eta = " << eta << endl;
        }
        
    }
    
    formuli.clear(); sum.clear();
    //delete sat;
    for (int i=0; i<igraph_ecount(G); i++)
        if (solution[e(i+1)] != l_False) { Edge edge; igraph_edge(G, i, &edge.first, &edge.second); self->H->del_edge(edge); }
    
    //	Grabage Collection
    for (int i =0; i < igraph_vector_ptr_size(&match_vert); i++)
        igraph_vector_destroy((igraph_vector_t*) VECTOR(match_vert)[i]);
    igraph_vector_ptr_destroy(&match_vert);
    
}

void Security::df(igraph_vector_t* v, igraph_t* g, int vert, int vert1, int d)
{
    igraph_vector_t neis;
    igraph_vector_init(&neis, 0);
    igraph_neighbors(G, &neis, vert, IGRAPH_OUT);
    for (int k=0; k < igraph_vector_size(&neis); k++)
        //		igraph_vector_push_back(verts, VECTOR(neis)[k]);
        if (igraph_ecount(g) < d)
        {
            if (VAN(G, "traversed", VECTOR(neis)[k]) || VAN(G, "removed", VECTOR(neis)[k])) continue;
            igraph_vector_push_back(v, VECTOR(neis)[k]);
            igraph_add_vertices(g, 1, 0);
            SETVAN(g, "colour", igraph_vcount(g) - 1, VAN(G, "colour", VECTOR(neis)[k]));
            
            igraph_add_edge(g, vert1, igraph_vcount(g)-1);
            df(v, g, VECTOR(neis)[k], igraph_vcount(g)-1, d);
            
        }
    igraph_vector_destroy(&neis);
    igraph_vector_init(&neis, 0);
    igraph_neighbors(G, &neis, vert, IGRAPH_IN);
    for (int k=0; k < igraph_vector_size(&neis); k++)
        //		igraph_vector_push_back(verts, VECTOR(neis)[k]);
        if (igraph_ecount(g) < d)
        {
            if (VAN(G, "traversed", VECTOR(neis)[k]) || VAN(G, "removed", VECTOR(neis)[k])) continue;
            igraph_vector_push_back(v, VECTOR(neis)[k]);
            igraph_add_vertices(g, 1, 0);
            SETVAN(g, "colour", igraph_vcount(g) - 1, VAN(G, "colour", VECTOR(neis)[k]));
            
            igraph_add_edge(g, igraph_vcount(g)-1,  vert1);
            df(v, g, VECTOR(neis)[k], igraph_vcount(g)-1, d);
            
        }
    igraph_vector_destroy(&neis);
}

void Security::kiso(int min_L1, int max_L1) {
    
    
    int maxPAGsize = 0;
    igraph_vector_t res;
    igraph_vector_init(&res, 0);
    igraph_vs_t vs;
    igraph_vs_all(&vs);
    igraph_degree(G, &res, vs, IGRAPH_ALL, false);
    for (int i=0; i < igraph_vector_size(&res); i++)
        maxPAGsize+=igraph_vector_e(&res, i);
    maxPAGsize=maxPAGsize/igraph_vcount(G);
    //	maxPAGsize=10;
    //	cout << "PAG size: " << maxPAGsize << endl;
    
    
    igraph_vector_ptr_t pags;
    igraph_vector_ptr_init(&pags, 0);
    
    igraph_vector_ptr_t embeds;
    igraph_vector_ptr_init(&embeds, 0);
    igraph_vector_ptr_t maps;
    igraph_vector_ptr_init(&maps, 0);
    
    igraph_vector_ptr_t ids;
    igraph_vector_ptr_init(&ids, 0);
    
    igraph_vector_t maxdeg;
    igraph_vector_t maxcount;
    igraph_vector_init(&maxdeg, 0);
    igraph_vector_init(&maxcount, 0);
    
    // cout << "Average vertex degree: " << maxPAGsize << endl;
    igraph_vector_ptr_t vm;
    igraph_vector_ptr_init(&vm, min_L1);
    
    for (int i = 0; i < igraph_vcount(G); i++) SETVAN(G, "removed", i, false);
    
    for (int i=0; i < min_L1; i++) {
        VECTOR(vm)[i] = new igraph_vector_t;
        igraph_vector_init( (igraph_vector_t*) VECTOR(vm)[i], 0);
    }
    
    while (igraph_vcount(G) != 0) {
        for (int i=0; i < igraph_vcount(G); i++)
        {
            //			cout << i << endl;
            ;
            if (VAN(G, "removed", i)) continue;
            //			igraph_vector_t vert;
            igraph_vs_t vs;
            
            //			igraph_vector_init(&vert, 0);
            igraph_vector_t v;
            igraph_vector_init(&v, 1);
            VECTOR(v)[0] = i;
            igraph_t res1;
            igraph_empty(&res1, 1, 0);
            SETVAN(&res1, "colour", 0, VAN(G, "colour", i));
            
            for (int mm = 0; mm < igraph_vcount(G); mm++) SETVAN(G, "traversed", mm, false);
            SETVAN(G, "traversed", i, true);
            
            df(&v, &res1, i, 0, maxPAGsize);
            if (igraph_ecount(&res1) < maxPAGsize) continue;
            //			igraph_vector_destroy(&vert);
            //			for (int j=0; j < igraph_vector_ptr_size(&v); j++)
            {
                //			igraph_vs_vector(&vs	, (igraph_vector_t*) VECTOR(v)[j]);
                igraph_vs_vector(&vs	, &v);
                //			igraph_t res1;
                //			igraph_induced_subgraph(G, &res1, vs, IGRAPH_SUBGRAPH_CREATE_FROM_SCRATCH);
                
                bool found = false;
                igraph_vector_t color11;
                igraph_vector_init(&color11, 0);
                VANV(&res1, "colour", (igraph_vector_t*) &color11);
                igraph_vector_int_t color1;
                igraph_vector_int_init(&color1, 0);
                for (int m=0; m < igraph_vector_size(&color11); m++)
                    igraph_vector_int_push_back(&color1, VECTOR(color11)[m]);
                igraph_vs_destroy(&vs);
                for (int k=0; k < igraph_vector_ptr_size(&pags); k++)
                {
                    if (igraph_vcount(&res1) != igraph_vcount( (igraph_t*) VECTOR(pags)[k])) continue;
                    igraph_bool_t iso;
                    igraph_vector_t color22;
                    igraph_vector_init(&color22, 0);
                    VANV((igraph_t*) VECTOR(pags)[k], "colour", (igraph_vector_t*) &color22);
                    igraph_vector_int_t color2;
                    igraph_vector_int_init(&color2, 0);
                    for (int m=0; m < igraph_vector_size(&color22); m++)
                        igraph_vector_int_push_back(&color2, VECTOR(color22)[m]);
                    
                    igraph_vector_t* map12 = new igraph_vector_t;
                    igraph_vector_init(map12, 0);
                    //				if (igraph_vector_int_size(&color1) != igraph_vcount(&res1)) cout << 1 << " " << igraph_vector_size((igraph_vector_t*) &color1) << " " << igraph_vcount(&res1);
                    //				if (igraph_vector_int_size(&color2) != igraph_vcount((igraph_t*) VECTOR(pags)[k])) cout << 2; cout.flush();
                    igraph_isomorphic_vf2((igraph_t*) VECTOR(pags)[k], &res1, &color2, &color1, NULL, NULL, &iso, map12, NULL, NULL, NULL, NULL);
                    if (iso)
                    {
                        //					if (iso) cout << "true" << endl;
                        found = true;
                        igraph_vector_t* newv = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                        igraph_vector_copy(newv, &v);
                        igraph_vector_ptr_t* embedsi = (igraph_vector_ptr_t*)VECTOR(embeds)[k];
                        
                        // igraph_vector_ptr_push_back(embedsi, newv);
                        int hg = VECTOR(res)[(int) VECTOR(*newv)[0]];
                        for (int h=1; h < igraph_vector_size(newv); h++)
                            if (VECTOR(res)[(int) VECTOR(*newv)[h]] > hg) hg = VECTOR(res)[(int) VECTOR(*newv)[h]];
                        int l;
                        for (l=0; l < igraph_vector_ptr_size(embedsi); l++)
                        {
                            igraph_vector_t* fg = (igraph_vector_t*)VECTOR(*embedsi)[l];
                            int hh = VECTOR(res)[(int) VECTOR(*fg)[0]];
                            for (int h=1; h < igraph_vector_size(fg); h++)
                                if (VECTOR(res)[(int) VECTOR(*fg)[h]] > hh) hh = VECTOR(res)[(int) VECTOR(*fg)[h]];
                            if (hh > VECTOR(maxdeg)[k]) { VECTOR(maxcount)[k] = 1; VECTOR(maxdeg)[k] = hh; }
                            if (hh == VECTOR(maxdeg)[k]) { VECTOR(maxcount)[k] += 1; }
                            
                            if (hh < hg) break;
                        }
                        if (l == igraph_vector_ptr_size(embedsi)) {
                            igraph_vector_ptr_push_back(embedsi, newv);
                            igraph_vector_ptr_push_back((igraph_vector_ptr_t*)VECTOR(maps)[k], map12);
                        }
                        else { igraph_vector_ptr_insert(embedsi, l, newv);
                            igraph_vector_ptr_insert((igraph_vector_ptr_t*)VECTOR(maps)[k], l, map12); }
                    }
                    igraph_vector_int_destroy(&color2);
                    igraph_vector_destroy(&color22);
                }
                if (!found) {
                    igraph_t* temp = new igraph_t;
                    igraph_copy(temp, &res1);
                    igraph_vector_ptr_push_back(&pags, temp);
                    igraph_vector_t* newv = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                    igraph_vector_copy(newv, &v);
                    igraph_vector_ptr_t* newvv = (igraph_vector_ptr_t*) malloc(sizeof(igraph_vector_ptr_t));
                    igraph_vector_ptr_init(newvv,0);
                    igraph_vector_ptr_push_back(newvv, newv);
                    igraph_vector_ptr_push_back(&embeds, newvv);
                    newv = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                    igraph_vector_init(newv, 0);
                    for (int n=0; n < igraph_vcount(&res1); n++) igraph_vector_push_back(newv, n);
                    newvv = (igraph_vector_ptr_t*) malloc(sizeof(igraph_vector_ptr_t));
                    igraph_vector_ptr_init(newvv,0);
                    igraph_vector_ptr_push_back(newvv, newv);
                    igraph_vector_ptr_push_back(&maps, newvv);
                }
                igraph_destroy(&res1);
                igraph_vector_int_destroy(&color1);
                igraph_vector_destroy(&color11);
            }
            // for (int m=0; m<igraph_vector_ptr_size(&v); m++) igraph_vector_destroy((igraph_vector_t*)(VECTOR(v)[m]));
            igraph_vector_destroy(&v);
        }
        
        //			cout << igraph_vector_ptr_size(&pags) << endl;
        //			cout << igraph_vector_ptr_size(&embeds) << endl;
        //			cout << igraph_vector_ptr_size(&maps) << endl;
        
        for (int k=0; k < igraph_vector_ptr_size(&pags); k++)
        {
            igraph_t* newg = (igraph_t*) malloc(sizeof(igraph_t));
            
            
            igraph_vector_ptr_push_back(&ids, newg);
            igraph_vector_ptr_t* embedsi = (igraph_vector_ptr_t*)VECTOR(embeds)[k];
            igraph_empty(newg, igraph_vector_ptr_size(embedsi), IGRAPH_UNDIRECTED);
            for (int l=0; l < igraph_vector_ptr_size(embedsi); l++)
            {
                for (int s=l+1; s < igraph_vector_ptr_size(embedsi); s++) {
                    igraph_vector_t* fg = (igraph_vector_t*)VECTOR(*embedsi)[l];
                    igraph_vector_t* fh = (igraph_vector_t*)VECTOR(*embedsi)[s];
                    for (int h=0; h < igraph_vector_size(fg); h++)
                    {
                        int found = false;
                        for (int g=0; g<igraph_vector_size(fh); g++)
                            if (VECTOR(*fg)[h]==VECTOR(*fh)[g]) {
                                found = true;
                                igraph_add_edge((igraph_t*) VECTOR(ids)[k], l, s);
                                break;
                            }
                        if (found) break;
                    }
                }
            }
            
        }
        
        //			cout << igraph_vector_ptr_size(&ids) << endl;
        
        //		cout << "first time" << endl;
        while(1) {
            igraph_vector_ptr_t vd_embeds;
            igraph_vector_ptr_init(&vd_embeds, 0);
            
            for (int i = 0; i < igraph_vector_ptr_size(&ids); i++)
            {
                igraph_vector_ptr_t idss;
                igraph_vector_ptr_init(&idss, 0);
                igraph_vector_t* newv; // = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                //igraph_vector_init(newv, 0);
                //				cout << igraph_vcount((igraph_t*) VECTOR(ids)[i]) << " "; cout.flush();
                bool foundy = false;
                for (int j=0; j < igraph_vcount((igraph_t*) VECTOR(ids)[i]); j++)
                {
                    newv = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                    igraph_vector_init(newv, 0);
                    igraph_vector_push_back(newv, j);
                    p1((igraph_t*) VECTOR(ids)[i], newv, min_L1);
                    if (igraph_vector_size(newv) >= min_L1) { foundy = true; break; }
                    
                    for (int r=1; r <= min_L1; r++) { for (int k=1; k <= r; k++) { p2((igraph_t*) VECTOR(ids)[i], newv, min_L1); if (igraph_vector_size(newv) >= min_L1) { foundy=true; break; } } if (foundy) break; }
                    if (foundy) break;
                    igraph_vector_ptr_push_back(&idss, newv);
                }
                
                if (foundy) { igraph_vector_ptr_push_back(&vd_embeds, newv); for (int m=0; m < igraph_vector_ptr_size(&idss); m++) igraph_vector_destroy((igraph_vector_t*) VECTOR(idss)[m]); igraph_vector_ptr_destroy(&idss); continue; }
                igraph_vector_t* result;
                
                // if (igraph_vector_ptr_size(&idss) == 0) cout << "yes" << endl; cout.flush();
                bool found00 = 0;
                for (int j=0; j < igraph_vector_ptr_size(&idss); j++)
                {
                    for (int k=0; k < igraph_vector_ptr_size(&idss); k++)
                    {
                        result = (igraph_vector_t*) malloc(sizeof(igraph_vector_t));
                        igraph_vector_init(result, 0);
                        igraph_vector_sort((igraph_vector_t*) VECTOR(idss)[k]); igraph_vector_sort((igraph_vector_t*) VECTOR(idss)[j]);
                        igraph_vector_intersect_sorted((igraph_vector_t*) VECTOR(idss)[k], (igraph_vector_t*) VECTOR(idss)[j], result);
                        p1((igraph_t*) VECTOR(ids)[i], result, min_L1);
                        if (igraph_vector_size(result) >= min_L1) { found00 = 1; break; }
                        for (int r=1; r <= min_L1; r++) { for (int l=1; l <= r; l++) { p2((igraph_t*) VECTOR(ids)[i], result, min_L1); if (igraph_vector_size(result) >= min_L1) { found00 = 1; break; } } if (found00) break; }
                        if (found00) break;
                        igraph_vector_destroy(result);
                    }
                    if (found00) break;
                }
                if (found00) { igraph_vector_ptr_push_back(&vd_embeds, result); continue; }
                igraph_vector_ptr_push_back(&vd_embeds, NULL);
                //				cout << "NULL";
            }
            
            //			cout << igraph_vector_ptr_size(&ids) << endl;
            
            //	igraph* kgraphs = new igraph_t[min_L1];
            //	for (int i = 1; i <= min_L1; i++)
            //	{
            //		igraph_empty(kgraphs[i], 0, UNDIRECTED);
            //	}
            
            int max=0, maxe=-1;
            int id; bool found=false;
            for (int i=0; i < igraph_vector_ptr_size(&pags); i++)
            {
                if (VECTOR(vd_embeds)[i] == NULL) continue;
                found = true;
                if (igraph_ecount((igraph_t*) VECTOR(pags)[i]) > maxe) { maxe = igraph_ecount((igraph_t*) VECTOR(pags)[i]); id = i; max = VECTOR(maxdeg)[i];  continue; }
                
                if (igraph_ecount((igraph_t*) VECTOR(pags)[i]) == maxe) {
                    if (VECTOR(maxdeg)[i] > max) {  id = i; max = VECTOR(maxdeg)[i]; }
                    else if (VECTOR(maxdeg)[i] == max) if (VECTOR(maxcount)[i] > VECTOR(maxcount)[id]) id = i; }
            }
            if (!found) {
                for (int c=0; c < igraph_vector_ptr_size(&pags); c++) { igraph_destroy((igraph_t*) VECTOR(pags)[c]); igraph_destroy((igraph_t*) VECTOR(ids)[c]); }
                //				igraph_vector_ptr_destroy(&pags); igraph_vector_ptr_destroy(&ids);
                //				igraph_vector_ptr_init(&pags, 0); igraph_vector_ptr_init(&ids, 0);
                for (int c=0; c < igraph_vector_ptr_size(&embeds); c++)
                    for (int b=0; b < igraph_vector_ptr_size((igraph_vector_ptr_t*) VECTOR(embeds)[c]); b++) {
                        igraph_vector_destroy((igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(embeds)[c])[b]);
                        igraph_vector_destroy((igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(maps)[c])[b]);
                    }
                //				igraph_vector_ptr_init(&embeds, 0);
                //				igraph_vector_ptr_init(&maps, 0);
                //				igraph_vector_destroy(&maxdeg);
                //				igraph_vector_destroy(&maxcount);
                
                igraph_vector_ptr_clear(&pags); igraph_vector_ptr_clear(&ids);
                igraph_vector_ptr_clear(&embeds);
                igraph_vector_ptr_clear(&maps);
                
                igraph_vector_clear(&maxdeg);
                igraph_vector_clear(&maxcount);
                
                //				igraph_vector_init(&maxdeg, 0);
                //				igraph_vector_init(&maxcount, 0);
                
                break;
            }
            //			cout << "id: " << id << endl;
            for (int i=0; i < min_L1; i++) {
                //				cout << i << endl; cout.flush();
                //if (VECTOR(vd_embeds)[id] == NULL) cout << "yes"; cout << igraph_vector_size((igraph_vector_t*)VECTOR(vd_embeds)[id]); cout.flush();
                //cout << (int) VECTOR(*(igraph_vector_t*)VECTOR(vd_embeds)[id])[i]; cout.flush();
                igraph_vector_t* one = (igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(embeds)[id]) [(int) VECTOR(*(igraph_vector_t*)VECTOR(vd_embeds)[id])[i]];
                igraph_vector_t* two = (igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(maps)[id]) [(int) VECTOR(*(igraph_vector_t*)VECTOR(vd_embeds)[id])[i]];
                igraph_vector_t third; igraph_vector_init(&third,0);
                for (int j=0; j < igraph_vector_size(one); j++)
                {
                    //	cout << VECTOR(*one)[j]<< endl;cout.flush();
                    long int pos;
                    igraph_vector_search(two, 0, j, &pos);
                    //					igraph_vector_swap_elements(one, j, pos);
                    igraph_vector_push_back(&third,VECTOR(*one)[pos]);
                }
                igraph_vector_update(one, &third);
                igraph_vector_append( (igraph_vector_t*) VECTOR(vm)[i], one);
                
                igraph_vs_t vertices;
                igraph_vs_vector(&vertices, one);
                for (int s=0; s < igraph_vector_size(one); s++) SETVAN(G, "removed", VECTOR(*one)[s], true);
                // igraph_delete_vertices(H, vertices);
                igraph_vs_destroy(&vs);
                
                for (int j=0; j < igraph_vector_ptr_size(&embeds); j++)
                {
                    igraph_vector_t vecto; igraph_vector_init(&vecto, 0);
                    for (int k=0; k < igraph_vector_size((igraph_vector_t*) VECTOR(embeds)[j]); k++)
                    {
                        bool found123 = false;
                        for (int h=0; h < igraph_vector_size((igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(embeds)[j])[k]); h++)
                        {
                            for (int l=0; l < igraph_vector_size(one); l++)
                                if (VECTOR(*(igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(embeds)[j])[k])[h] ==
                                    VECTOR(*one)[l])
                                { igraph_vector_ptr_remove((igraph_vector_ptr_t*) VECTOR(embeds)[j], k);
                                    igraph_vector_ptr_remove((igraph_vector_ptr_t*) VECTOR(maps)[j], k);
                                    igraph_vector_push_back(&vecto, k);
                                    k--; found123 = true; break; }
                            if (found123) break;
                        }
                    }
                    
                    igraph_t* newg = (igraph_t*) malloc(sizeof(igraph_t));
                    igraph_destroy( (igraph_t*) VECTOR(ids)[j]);
                    
                    // igraph_vector_ptr_push_back(&ids, newg);
                    igraph_vector_ptr_t* embedsi = (igraph_vector_ptr_t*)VECTOR(embeds)[j];
                    igraph_empty(newg, igraph_vector_ptr_size(embedsi), IGRAPH_UNDIRECTED);
                    for (int l=0; l < igraph_vector_ptr_size(embedsi); l++)
                    {
                        for (int s=l+1; s < igraph_vector_ptr_size(embedsi); s++) {
                            igraph_vector_t* fg = (igraph_vector_t*)VECTOR(*embedsi)[l];
                            igraph_vector_t* fh = (igraph_vector_t*)VECTOR(*embedsi)[s];
                            for (int h=0; h < igraph_vector_size(fg); h++)
                            {
                                int found = false;
                                for (int g=0; g<igraph_vector_size(fh); g++)
                                    if (VECTOR(*fg)[h]==VECTOR(*fh)[g]) {
                                        found = true;
                                        igraph_add_edge(newg, l, s);
                                        break;
                                    }
                                if (found) break;
                            }
                        }
                    }
                    igraph_copy((igraph_t*) VECTOR(ids)[j], newg);
                    //igraph_vs_t vid;
                    //igraph_vs_vector(&vid, &vecto);
                    //igraph_delete_vertices((igraph_t*) VECTOR(ids)[j], vid);
                    //igraph_vs_destroy(&vid); igraph_vector_destroy(&vecto);
                }
                
                for (int j=0; j < igraph_vector_ptr_size(&embeds); j++)
                {
                    int maxdeggg = 0, counto = 0;
                    for (int k=0; k < igraph_vector_size((igraph_vector_t*) VECTOR(embeds)[j]); k++)
                    {
                        int maxdegg = 0;
                        for (int h=0; h < igraph_vector_size((igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(embeds)[j])[k]); h++)
                        {
                            
                            if (maxdegg < VECTOR(res)[(int) VECTOR(*(igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(embeds)[j])[k])[h]]) maxdegg = VECTOR(res)[(int) VECTOR(*(igraph_vector_t*) VECTOR(*(igraph_vector_ptr_t*) VECTOR(embeds)[j])[k])[h]];
                        }
                        if (maxdegg > maxdeggg) { maxdeggg = maxdegg; counto = 1; }
                        if (maxdeggg == maxdegg) counto++;
                    }
                    VECTOR(maxdeg)[j] = maxdeggg; VECTOR(maxcount)[j] = counto;
                }
                
            }
            
            for (int m=0; m < igraph_vector_ptr_size(&vd_embeds); m++) if ( VECTOR(vd_embeds)[m] != NULL )igraph_vector_destroy((igraph_vector_t*) VECTOR(vd_embeds)[m]); igraph_vector_ptr_destroy(&vd_embeds);
        }
        //		cout << "here" << endl;
        maxPAGsize--;
        if (maxPAGsize < 0) break;
        
        bool found = false;
        int count = 0;
        for (int c=0; c < igraph_vcount(G); c++) if (!VAN(G, "removed", c)) { found = true; count++; /* break; */ };
        //		cout << count << endl;
        if (!found) break;
    }
    
    //igraph_destroy(G);
    //igraph_copy(G, H);
    int r = igraph_vector_size((igraph_vector_t*) VECTOR(vm)[0]);
    for (int j = 0; j < r; j++)
    {
        for (int k = 0; k < r; k++)
        {
            if (j==k) continue;
            int eid;
            bool found = false;
            for (int i=0; i < min_L1; i++)
            {
                igraph_get_eid(G, &eid, VECTOR(*(igraph_vector_t*) VECTOR(vm)[i])[j], VECTOR(*(igraph_vector_t*) VECTOR(vm)[i])[k], IGRAPH_DIRECTED, false);
                if (eid == -1) { found = true; break; }
            }
            if (!found) for (int i=0; i < min_L1; i++) igraph_add_edge(H, VECTOR(*(igraph_vector_t*) VECTOR(vm)[i])[j], VECTOR(*(igraph_vector_t*) VECTOR(vm)[i])[k]);
        }
    }
    
    cout << igraph_ecount(G)-igraph_ecount(H) << " " << min_L1 <<endl;
}

void Security::p1(igraph_t* G, igraph_vector_t* ids, int min_L1)
{
    int max=0, v;
    int found1=false;
    for (int i = 0; i < igraph_vcount(G); i++)
    {
        if (igraph_vector_contains(ids, i)) continue;
        int found = false;
        int j;
        for (j=0; j < igraph_vector_size(ids); j++)
        {
            int eid;
            igraph_get_eid(G, &eid, i, VECTOR(*ids)[j], false, false);
            if (eid != -1) { found = true; break; };
        }
        if (!found) {
            found1=true;
            igraph_vector_push_back(ids, i);
            if (igraph_vector_size(ids) >= min_L1) return;
            int g = count(G, ids);
            if (g >= max) { v = i; max = g; }
            igraph_vector_pop_back(ids);
        }
    }
    if (!found1) return;
    else { igraph_vector_push_back(ids, v); p1(G, ids, min_L1); }
}

int Security::count(igraph_t* G, igraph_vector_t* ids)
{
    int c = 0;
    for (int i = 0; i < igraph_vcount(G); i++)
    {
        if (igraph_vector_contains(ids, i)) continue;
        bool found = false;
        for (int j=0; j < igraph_vector_size(ids); j++)
        {
            int eid;
            igraph_get_eid(G, &eid, i, VECTOR(*ids)[j], false, false);
            if (eid != -1) { found = true; break; };
        }
        if (!found) c++;
        
    }
    return c;
}

void Security::p2(igraph_t* G, igraph_vector_t* ids, int min_L1)
{
    for (int i = 0; i < igraph_vcount(G); i++)
    {
        if (igraph_vector_contains(ids, i)) continue;
        int count = 0;
        int j=0;
        for (j=0; j < igraph_vector_size(ids); j++)
        {
            int eid;
            igraph_get_eid(G, &eid, i, VECTOR(*ids)[j], false, false);
            if (eid != -1) { count++; if (count > 1) break; };
        }
        if (count == 1) {igraph_vector_remove(ids, j); igraph_vector_push_back(ids, i); p1(G, ids, min_L1); break;}
        
    }
}

/*************************************************************************//**
                                                                            * @brief
                                                                            * @version						v0.01b
                                                                            ****************************************************************************/
void Security::S1_greedy (bool save_state, int threads, int min_L1, int max_L1, bool quite) { // Added by Karl (int remove_vertex_max)
    
    /******************************
     * Setup
     ******************************/
    // Added by Karl
    //    if(save_state) {
    //        k2outfile.open("gnuplotOutput/test.txt");
    //        k2outfile<<"# security"<<"     "<<"# lifted e"<<endl;
    //    }
    ////////////////
    
    if (max_L1 == -1) max_L1 = G->max_L1();
    if (igraph_ecount(H) == 0) add_free_edges(max_L1);
    
    vector<L1_Edge*> edges;
    vector<L1_Edge*> edge_list;
    for (unsigned int eid = 0; eid < igraph_ecount(G); eid++)
        if (!H->test_edge(G->get_edge(eid)) && !(EAN(G,"Lifted",eid) == Lifted)) {// edges already in H will not be considered in the list of candidates as well as edges that are connected to lifted vertices
            int from, to;
            igraph_edge(G, eid, &from, &to);
            edges.push_back( new L1_Edge(eid, Edge(from,to), max_L1) );
            edge_list.push_back( edges.back() );
        }
    
#ifndef NRAND
    random_shuffle(edge_list.begin(), edge_list.end());
#endif
    
#ifdef VF2
    bool vf2_flippy(false);
#endif
    vector<L1_Thread*> busy_threads, free_threads;
    for (unsigned int i=0; i<threads; i++) {
        free_threads.push_back( new L1_Thread() );
#ifdef VF2
        if (vf2_flippy)
            free_threads.back()->vf2 = true;
        vf2_flippy = !vf2_flippy;
#endif
    }
    
    /******************************
     * Add edges until L1 == min_L1
     ******************************/
    
    //	Added by Mohamed
    int prev_L1 = max_L1;
    
    ofstream myfile;
    myfile.open ("tradeoff.dat");
    
    /*
     // Added by Karl
     L1_Edge *worst_edge = edge_list[0];
     bool find_worst = false;
     int remove_vertex = 0;
     //int remove_vertex_max = 2;
     
     if (remove_vertex_max)
     find_worst = true;
     ////////////////
     */
    while ((max_L1 >= min_L1 || max_L1 == -2) && edge_list.size() > 0) { // Added by Karl: || max_L1 == -2 to account for inf lvl graphs
        
        cout << "  E(" << edge_list.size() << ") ";
        cout.flush();
        
        /******************************
         * Presort eids int max(L1)
         ******************************/
        L1_Edge *best_edge = edge_list[0];
        sort    (edge_list.begin(), edge_list.end(), l1_edge_lt);
        reverse (edge_list.begin(), edge_list.end());
        int sat_index(0), vf2_index(0);
        
#ifdef DEBUG
        cout << endl << "edge_list.sort(" << edge_list.size() << ") : ";
        for (unsigned int i = 0; i < edge_list.size(); i++)
            cout << "(" << edge_list[i]->eid << ", " << edge_list[i]->L1_prev << "," << edge_list[i]->L1_sat << "," << edge_list[i]->L1_vf2 << ") ";
        cout << endl;
#endif
        
        while (sat_index < edge_list.size()) {
            
            /******************************
             * Load Threads (create sub-processes)
             ******************************/
            if (free_threads.size() > 0) {
                busy_threads.push_back(free_threads.back());
                free_threads.pop_back();
                
                if (busy_threads.back()->vf2)
                    if (vf2_index >= edge_list.size())
                        busy_threads.back()->vf2 = false;
                
                if (busy_threads.back()->vf2) {
                    busy_threads.back()->test_edge = edge_list[vf2_index++];
                } else {
                    busy_threads.back()->test_edge = edge_list[sat_index++];
                }
                
                busy_threads.back()->open(true,false);
                
                /******************************
                 * Child
                 ******************************/
                if ( busy_threads.back()->child() ) {              // Child (PID == 0)
                    
                    L1_Edge *test_edge = busy_threads.back()->test_edge;
                    
#ifdef MEASURE_TIME_S1
                    clock_t tic = clock();
#endif
                    //if (!((test_edge->edge.first == 1) || (test_edge->edge.second == 1))) {
                    add_edge(test_edge->eid);
                    //} else
                    //  cout<<"Vertex 1"<<endl;
                    
#ifdef DEBUG
                    cout << endl;
                    cout << "Child(" << getpid() << ") : before clean "<< solutions.size() << endl;
#endif
                    clean_solutions();
                    
#ifdef DEBUG
                    cout << "Child(" << getpid() << ") :  after clean "<< solutions.size() << endl;
#endif
                    int old_size = solutions.size();
#ifdef MEASURE_TIME_S1
                    clock_t toc = clock();
#ifdef DEBUG
                    cout << "Child(" << getpid() << ") :   time clean ";
                    << (double) (toc-tic)/CLOCKS_PER_SEC << endl;
#endif
#endif
                    
                    if (busy_threads.back()->vf2) { // Can we improve the best case lvl so far by adding an edge to this graph? If the lvl is already lower or equal then noway, otherwise we might.
                        if (test_edge->L1_prev < min_L1)
                            test_edge->L1_vf2 = 1;
                        if (test_edge->L1_prev <= best_edge->L1())
                            test_edge->L1_vf2 = test_edge->L1_prev;
                        else
                            test_edge->L1_vf2 = L1(true, true);
                    } else {
                        if (test_edge->L1_prev < min_L1 && test_edge->L1_prev > -2) // Added by Karl: && test_edge->L1_prev > -2
                            test_edge->L1_sat = 1;
                        if (test_edge->L1_prev <= best_edge->L1() && test_edge->L1_prev > -2) // Added by Karl: && test_edge->L1_prev > -2 // shouldn't we add an else otherwise everytime the first if is met, this one will and it will change the L1_sat
                            test_edge->L1_sat = test_edge->L1_prev;
                        else
                            test_edge->L1_sat = L1();
                    }
                    
                    string output;
                    if (busy_threads.back()->vf2) {
                        output = "S1_greedy.vf2 ("  + G->get_name() + ").child(" + num2str(getpid()) + ")";
                        output = report(output, G, H, test_edge->L1_vf2, solutions.size(), test_edge->edge);
                    } else {
                        output = "S1_greedy.sat ("  + G->get_name() + ").child(" + num2str(getpid()) + ")";
                        output = report(output, G, H, test_edge->L1_sat, solutions.size(), test_edge->edge);
                    }
                    
#ifdef DEBUG
                    cout << output;
#endif
                    
#ifdef USE_SOLNS
                    vector<igraph_vector_t*>::iterator it_begin = solutions.begin();
                    for (unsigned int i = 0; i < old_size; i++) {
                        it_begin++;
                        if (it_begin == solutions.end()) break;
                    }
                    for (vector<igraph_vector_t*>::iterator it = it_begin; it != solutions.end(); ++it)
                        output += report(*it);
#endif
                    
                    busy_threads.back()->write(output);
                    
                    busy_threads.back()->close(false, true);
                    
#ifdef MEASURE_TIME_S1
                    toc = clock();
                    cout << endl << "Child(" << getpid() << ") : Total Time: ";
                    cout << (double) (toc-tic)/CLOCKS_PER_SEC << endl;
#endif
                    
                    _exit(0);
                }
            }
            
            /******************************
             * Unload Threads (Parent)
             ******************************/
            do {
                
                for (unsigned int j=0; j<busy_threads.size(); j++) {
                    string response = busy_threads[j]->read();
                    // do something with response
                    if (response.size() > 0) {
                        
#ifdef MEASURE_TIME_S1
                        clock_t tic = clock();
#endif
                        
                        L1_Edge *test_edge = busy_threads[j]->test_edge;
                        int L0;
                        
                        stringstream r_stream(response);
                        string line;
                        while( getline(r_stream, line) ) {
                            
                            Edge tmp;
                            if (busy_threads[j]->vf2) {
                                parse(line, G, test_edge->L1_vf2, L0, tmp);
                                test_edge->L1_vf2 = min(max_L1, test_edge->L1_vf2);
                            } else {
                                parse(line, G, test_edge->L1_sat, L0, tmp);
                                test_edge->L1_sat = min(max_L1, test_edge->L1_sat);
                            }
                            
#ifdef USE_SOLNS
                            // recive solutions
                            igraph_vector_t *map21 = new igraph_vector_t();
                            igraph_vector_init (map21, igraph_vcount(H));
                            if ( parse(line, map21) ) {
                                solutions.push_back(map21);
                            } else {
                                igraph_vector_destroy (map21);
                                delete map21;
                            }
#endif
                            
                        }
                        
                        // Store best results
                        if ((test_edge->L1() > best_edge->L1()) || (test_edge->L1() != best_edge->L1() && test_edge->L1() == -2)) { //Added by Karl: || (test_edge->L1() != best_edge->L1() && test_edge->L1() == -2. We want them to be different when == -2 because if it's the same it means that both are inf lvl so no need to update, we can use the old edge.
                            best_edge = test_edge;
                        }
                        /*
                         // Added by Karl
                         if ((test_edge->L1() < worst_edge->L1()) && find_worst) {
                         worst_edge = test_edge;
                         }
                         ////////////////
                         */
                        if (busy_threads[j]->vf2)
                            cout << 'v';
                        else
                            cout << 's';
                        cout.flush();
                        
#ifdef DEBUG
                        string output;
                        if (busy_threads[j]->vf2) {
                            output = "S1_greedy.vf2 ("  + G->get_name() + ").parent(" + num2str(busy_threads[j]->pid) + ")";
                            output = report(output, G, H, test_edge->L1_vf2, solutions.size(), test_edge->edge);
                        } else {
                            output = "S1_greedy.sat ("  + G->get_name() + ").parent(" + num2str(busy_threads[j]->pid) + ")";
                            output = report(output, G, H, test_edge->L1_sat, solutions.size(), test_edge->edge);
                        }
                        cout << endl << output;
#endif
                        
                        free_threads.push_back(busy_threads[j]);
                        busy_threads.erase(busy_threads.begin()+j);
                        j = -1; // j++
                        
#ifdef MEASURE_TIME_S1
                        clock_t toc = clock();
                        cout << endl << "Parent: pipe Time: ";
                        cout << (double) (toc-tic)/CLOCKS_PER_SEC << endl;
#endif
                    }
                    //if (best_edge->L1() == max_L1) break;
                }
                //if (best_edge->L1() == max_L1) break;
                
            } while (free_threads.size() == 0);
            
            // were done, clean up threads
            //if (best_edge->L1() == max_L1)
            //  break;
        }
        
        // empty left over threads
        while (busy_threads.size() > 0) {
            if (busy_threads[0]->read().size() == 0 ) {
#ifdef DEBUG
                cout << "Parent: Kill left over thread(" << busy_threads[0]->pid << ")" << endl;
#endif
                busy_threads[0]->close(true, false);
                busy_threads[0]->kill();
            }
            free_threads.push_back(busy_threads[0]);
            busy_threads.erase(busy_threads.begin());
        }
        
        if (best_edge->L1() != prev_L1)
        {
            for (int m = prev_L1; m > best_edge->L1(); m--)
                myfile << igraph_ecount(H) - 1 << " " << m << endl;
            prev_L1 = best_edge->L1();
        }
        
        if (best_edge->L1() < min_L1 && best_edge->L1() != -2) // Added by Karl: && best_edge->L1() != -2
            break;
        
        // add to graph, remove from list, reset edges
        add_edge(best_edge->eid);
        max_L1 = best_edge->L1();
        // Added by Karl
        //L1_state.max_L1 = max_L1;
        maxL1 = max_L1;
        ////////////////
        /*
         // Added by Karl
         int vid = -1, vid_1 = -1, vid_2 = -1;
         //vector<int> indexes;
         vector<L1_Edge*> edge_list_updated;
         if (find_worst) {
         if ((worst_edge->edge.first == best_edge->edge.first)
         || (worst_edge->edge.first == best_edge->edge.second))
         vid = worst_edge->edge.second;
         else if ((worst_edge->edge.second == best_edge->edge.first)
         || (worst_edge->edge.second == best_edge->edge.second))
         vid = worst_edge->edge.first;
         else {
         srand(time(NULL));
         if(rand() % 2)
         vid = worst_edge->edge.second;
         else vid = worst_edge->edge.first;
         }
         #ifdef DEBUG
         cout<<"Vertex removed: "<<vid<<endl;
         #endif
         
         // If it works, make a function
         // delete vertex with id vid.
         // igraph_delete_vertices(H, igraph_vss_1(vid));
         // H->update();
         }
         ////////////////
         */
        int best_edge_index(-1);
        for (unsigned int i=0; i<edge_list.size(); i++) {
            if ( edge_list[i] == best_edge) best_edge_index = i;
            if ( edge_list[i]->L1() > 0 )   edge_list[i]->L1_prev = edge_list[i]->L1();
            /*
             // Added by Karl
             //            if (find_worst && ((edge_list[i]->edge.first == vid) || (edge_list[i]->edge.second == vid))) {
             //                indexes.push_back(i);
             //            }
             //            if ((!(find_worst && ((edge_list[i]->edge.first == vid) || (edge_list[i]->edge.second == vid))))
             //                || (!(edge_list[i] == best_edge))) {
             //                edge_list_updated.push_back(edge_list[i]);
             //            }
             if (find_worst)
             if (!((edge_list[i]->edge.first == vid) || (edge_list[i]->edge.second == vid))
             && !(edge_list[i] == best_edge)) {
             #ifdef DEBUG
             cout<<edge_list[i]->edge.first<<"   "<<edge_list[i]->edge.second<<endl;
             #endif
             edge_list_updated.push_back(edge_list[i]);
             #ifdef DEBUG
             cout<<edge_list_updated.back()->edge.first<<"   "<<edge_list_updated.back()->edge.second<<endl<<endl;
             #endif
             }
             ////////////////
             */
            edge_list[i]->L1_sat = -1;
            edge_list[i]->L1_vf2 = -1;
        }
        /*
         // Added by Karl
         if (!find_worst) //////////
         */
        edge_list.erase(edge_list.begin()+best_edge_index);
        /*
         // Added by Karl
         else {
         for (int i = 0; i < edge_list_updated.size(); i++)
         edge_list[i] = edge_list_updated[i];
         
         edge_list.erase(edge_list.begin()+edge_list_updated.size(), edge_list.end());
         }
         ////////////////
         */
        /*
         // Added by Karl
         //        cout<<"OKAAY"<<endl;
         //        for (int i = 0; i < indexes.size(); i++)
         //            edge_list.erase(edge_list.begin()+indexes[i]);
         //
         //        cout<<"OKAAY    2"<<endl;
         // Delete corresponding vertex and check that the security computation still works. Otherwise, delete the edge when saving the circuit.
         //igraph_delete_vertices(H, igraph_vss_1(vid));
         remove_vertex++;
         if (remove_vertex >= remove_vertex_max)
         find_worst = false;
         ////////////////
         */
        
#ifdef MEASURE_TIME_S1
        clock_t tic = clock();
#endif
#ifdef USE_SOLNS
        clean_solutions();
#endif
#ifdef MEASURE_TIME_S1
        clock_t toc = clock();
        cout << endl << "Master: clean_solution() Time: ";
        cout << (double) (toc-tic)/CLOCKS_PER_SEC << endl;
#endif
        
        string output;
        output = "S1_greedy ("  + G->get_name() + ")";
        output = report(output, G, H, best_edge->L1_prev, solutions.size(), best_edge->edge);
        cout << endl << output;
        
        // Added by Karl
        // To be done only for the first iteration not the ones used inside the lift vertex thing. Add a bool
        if (save_state) {
            k2outfile<<maxL1<<" "<<igraph_ecount(G)-igraph_ecount(H)<<endl;
            int temp_maxL1 = maxL1;
            int temp_lifted = igraph_ecount(G)-igraph_ecount(H);
            // Save netlist
            Circuit temp_H, temp_G;
            temp_H.copy(H);
            temp_G.copy(G);
            //            cout<<setfill('/')<<setw(300)<<"G"<<endl;
            //            G->print();
            //            cout<<setfill('/')<<setw(300)<<"H"<<endl;
            //            H->print();
            //clean_solutions();
            vector<igraph_vector_t*> temp_solutions;
            vector<long> solutions_add;
            //temp_solutions = solutions;
            cout<<"here solutions"<<endl;
//            for (int i = 0; i < solutions.size(); i++) {
//                temp_solutions.push_back(new igraph_vector_t());
//                *temp_solutions[i] = *solutions[i];
//                cout<<solutions[i]<<endl;
//                solutions_add.push_back((long)solutions[i]);
//                cout<<solutions_add[i]<<endl;
//                //memcpy(temp_solutions[i], solutions[i], sizeof(igraph_vector_t));
//            }
            //cout<<setfill('/')<<setw(200)<<temp_solutions[0]<<" "<<solutions[0]<<endl;
            // Lift vertices after best edge added
            cout<<setfill('/')<<setw(200)<<"lift"<<endl;
            lift_vertex(maxL1, threads);
            cout<<setfill('/')<<setw(200)<<"done"<<endl;
            // Write to file
            file(WRITE);
            if (maxL1 == temp_maxL1)
                k3outfile<<setfill(' ')<<setw(5)<<maxL1<<setfill(' ')<<setw(11)<<igraph_ecount(G)-igraph_ecount(H)<<endl;
            else k3outfile<<setfill(' ')<<setw(5)<<temp_maxL1<<setfill(' ')<<setw(11)<<temp_lifted<<endl;
            // Reload old netlist
            //            cout<<setfill('/')<<setw(300)<<"G after"<<endl;
            G->copy(&temp_G);
            //            G->print();
            //            cout<<setfill('/')<<setw(300)<<"H after"<<endl;
            H->copy(&temp_H);
            //            H->print();
            solutions.clear();
            //            solutions.resize(temp_solutions.size());
//            for (int i = 0; i < temp_solutions.size(); i++) {
//                //                if (i >= temp_solutions.size()) {
//                //                    int index = i==temp_solutions.size()?i:index;
//                //                    delete solutions.
//                //                }
//                //                else
//                //solutions.push_back(new igraph_vector_t());
//                solutions[i] = (igraph_vector_t*)solutions_add[i];
//                cout<<solutions[i]<<endl;
//                *solutions[i] = *temp_solutions[i];
//                //memcpy(temp_solutions[i], solutions[i], sizeof(igraph_vector_t));
//            }
//            while (solutions.size() > temp_solutions.size())
//                solutions.pop_back();
            //solutions.clear();
            //clean_solutions();
        }
        ////////////////
    }
    
    for (unsigned int i=0; i<edges.size(); i++)
        delete edges[i];
    
    myfile.close();
}

// Added by Karl
void Security::L1_main (string outFileName, int _remove_vertices_max, int threads, int min_L1, int max_L1, bool quite) {
    // create and open file
    //string outFile = "gnuplotOutput/v_" + outFileName + "_" + to_string(min_L1);
    //ofstream outfile(outFile.c_str());
    //outfile<<"# lifted v"<<"     "<<"# unlifted e"<<endl;
    // initialise L1 max in strcut
    //L1_state.max_L1 = -1;
    maxL1 = -1;
    //init_maap();
    //for (int i = 0; i < igraph_vcount(H); i++)
    //  levels.push_back(0);
    //levels.resize(igraph_vcount(H));
    // Add edges until target sec lvl reached
    //read_levels();
    //    string outFile = "gnuplotOutput/" + outFileName;
    //    ofstream koutfile(outFile.c_str());
    //    koutfile<<"# security"<<"     "<<"# lifted e"<<endl;
    string outFile = "gnuplotOutput/" + outFileName;
    file(OPEN, outFile);
    
    remove_vertices_max = _remove_vertices_max;
    
    S1_greedy(true, threads, min_L1, max_L1);
    //outfile<<setfill(' ')<<setw(5)<<0<<setfill(' ')<<setw(16)<<igraph_ecount(H)<<endl;
    //outfile<<0<<" "<<igraph_ecount(H)<<endl;
    //read_levels();
    
    //    solutions.clear();
    //     remove mappings that don't work
    //        for (int i = 0; i < remove_vertices_max; i++) {
    //            // remove mappings that don't work
    //            clean_solutions();
    //            lift_vertex(/*maxL1*/);
    //
    //            // Add edges until we reach the target sec lvl
    //            // remove mappings that don't work
    //            clean_solutions();
    //            if (maxL1 > min_L1)
    //                S1_greedy(threads, min_L1, maxL1);
    //
    //            //write to file
    //            //outfile<<setfill(' ')<<setw(5)<<i+1<<setfill(' ')<<setw(16)<<igraph_ecount(H)<<endl;
    //            //outfile<<i+1<<" "<<igraph_ecount(H)<<endl;
    //        }
    
    file(CLOSE);
}

void Security::lift_vertex(/*int max_L1*/) {
    
    //read_levels();
    
    int index = -1;
    int max_L1 = maxL1;
    //int min_L1 = maxL1;
    //cout<<"level: "<<max_L1<<endl;
    for (int i = 0; i < igraph_vcount(H); i++) {
        vector<int> deleted;
        if (VAN(H,"Lifted",i) == NotLifted) {
            // remove mappings that don't work
            clean_solutions();
            //solutions.clear();
            // Lift the vertex
            SETVAN(H, "Lifted", i, Lifted);
            // remove the edges before
            for (int j = 0; j < igraph_ecount(G); j++) { // G not H because we want to delete the edges in H and when doing so the ids will get rearranged so we can get segmentation falt. Also, when we add back the edges we are adding them back from G so we need to know their id in G.
                if (H->test_edge(G->get_edge(j))) { // If the edge is in H
                    int from, to;
                    igraph_edge(G,j,&from,&to);
                    if (from == i || to == i) {
                        deleted.push_back(j);
                        int eid;
                        igraph_get_eid(H, &eid, from, to, IGRAPH_DIRECTED, 1); // get id of the edge in H
                        igraph_delete_edges(H, igraph_ess_1(eid));
                    }
                }
            }
            
            // Compute new L1
            int level = L1();
            cout<<"index: "<<i<<" level: "<<level<<" max: "<<max_L1<<endl;
            // save result if > than the max_L1 acheived so far
            if (level >= max_L1) {
                max_L1 = level;
                index = i;
            } /*else if (level == max_L1) {
               cout<<levels[i]<<endl;
               if (levels[i] <= min_L1) {
               min_L1 = levels[i];
               index = i;
               }
               max_L1 = level;
               }*/
            // Unlift the vertex
            SETVAN(H, "Lifted", i, NotLifted);
            // add back removed edges
            for (int j = 0; j < deleted.size(); j++)
                add_edge(deleted[j]);
        }
    }
    if (index >= 0)
        SETVAN(H, "Lifted", index, Lifted);
    
    // delete edges from H and change value of lifted vertex in G
    for (int j = 0; j < igraph_ecount(G); j++) { // G not H because we want to delete the edges in H and when doing so the ids will get rearranged so we can get segmentation falt. Also, when we add back the edges we are adding them back from G so we need to know their id in G.
        if (H->test_edge(G->get_edge(j))) { // If the edge is in H
            int from, to;
            igraph_edge(G,j,&from,&to);
            if (from == index || to == index) {
                int eid;
                igraph_get_eid(H, &eid, from, to, IGRAPH_DIRECTED, 1); // get id of the edge in H
                igraph_delete_edges(H, igraph_ess_1(eid));
                //igraph_get_eid(G, &eid, from, to, IGRAPH_DIRECTED, 1); // get id of the edge in H
                SETEAN(G, "Lifted", j, Lifted);
            }
        }
    }
    //temp
    //L1_state.max_L1 = max_L1;
    maxL1 = max_L1;
}

void Security::lift_vertex(int min_L1, int threads) {
    for (int i = 0; i < remove_vertices_max; i++) {
        // remove mappings that don't work
        clean_solutions();
        lift_vertex();
        
        // Add edges until we reach the target sec lvl
        // remove mappings that don't work
        clean_solutions();
        if (maxL1 > min_L1)
            S1_greedy(false, threads, min_L1, maxL1);
        
        //write to file
        //outfile<<setfill(' ')<<setw(5)<<i+1<<setfill(' ')<<setw(16)<<igraph_ecount(H)<<endl;
        //outfile<<i+1<<" "<<igraph_ecount(H)<<endl;
    }
    
}

void Security::file(actions action, string outFileName) {
    switch (action) {
        case OPEN:
            koutfile.open(outFileName.c_str());
            koutfile<<"# security"<<"     "<<"# lifted e"<<endl;
            
            k2outfile.open(string(outFileName.substr(0,outFileName.rfind('.')) + "_no_lifting.txt").c_str());
            k2outfile<<"# security"<<"     "<<"# lifted e"<<endl;
            
            k3outfile.open(string(outFileName.substr(0,outFileName.rfind('.')) + "_exact_sec_lvl.txt").c_str());
            k3outfile<<"# security"<<"     "<<"# lifted e"<<endl;
            break;
            
        case WRITE:
            koutfile<<setfill(' ')<<setw(5)<<maxL1<<setfill(' ')<<setw(11)<<igraph_ecount(G)-igraph_ecount(H)<<endl;
            break;
            
        case CLOSE:
            koutfile.close();
            break;
            
        default:
            break;
    }
}

void Security::init_maap() {
    for (int i = 0; i < igraph_vcount(H); i++)
        write_levels(i, -5);
}

void Security::write_levels(int vid2, int l) {
    fd = open(FILEPATH, O_RDWR | O_CREAT | O_TRUNC, (mode_t)0600);
    if (fd == -1) {
        perror("Error opening file for writing");
        exit(EXIT_FAILURE);
    }
    
    result = lseek(fd, igraph_vcount(H), SEEK_SET);
    if (result == -1) {
        close(fd);
        perror("Error calling lseek() to 'stretch' the file");
        exit(EXIT_FAILURE);
    }
    
    result = write(fd, "", 1);
    if (result != 1) {
        close(fd);
        perror("Error writing last byte of the file");
        exit(EXIT_FAILURE);
    }
    
    maap = (int*)mmap(0, igraph_vcount(H), PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    if (maap == MAP_FAILED) {
        close(fd);
        perror("Error mmapping the file");
        exit(EXIT_FAILURE);
    }
    
    maap[vid2] = l;
    
    if (munmap(maap, igraph_vcount(H)) == -1) {
        perror("Error un-mmapping the file");
    }
    close(fd);
    
}

void Security::read_levels() {
    fd = open(FILEPATH, O_RDONLY);
    if (fd == -1) {
        perror("Error opening file for reading");
        exit(EXIT_FAILURE);
    }
    
    maap = (int*)mmap(0, igraph_vcount(H), PROT_READ, MAP_SHARED, fd, 0);
    if (maap == MAP_FAILED) {
        close(fd);
        perror("Error mmapping the file");
        exit(EXIT_FAILURE);
    }
    
    /* Read the file int-by-int from the mmap
     */
    for (int i = 0; i <=igraph_vcount(H); i++) {
        cout<<i<<" "<<maap[i]<<endl;
    }
    
    if (munmap(maap, igraph_vcount(H)) == -1) {
        perror("Error un-mmapping the file");
    }
    close(fd);
}
////////////////
