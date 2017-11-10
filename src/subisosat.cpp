
/****************************************************************************//**
 ********************************************************************************
 * @file        subisosat.cpp
 * @brief       
 * @author      Frank Imeson
 * @date        
 ********************************************************************************
 ********************************************************************************/


#include "subisosat.hpp"

//#define DEBUG
//#define DEBUG_SAT
//#define MINISAT_VERBOSE


/*****************************************************************************
 *****************************************************************************
 * 
 * iGraph Functions
 *         
 *****************************************************************************
 *****************************************************************************/


/************************************************************//**
 * @brief	
 * @return            string representation of connective	
 * @version						v0.01b
 ****************************************************************/
int igraph_vertex_degree (const igraph_t *graph1, const igraph_integer_t vid)
{
    igraph_vector_t degree;
    igraph_vector_init(&degree, 1);
    igraph_vs_t vs;
    igraph_vs_1(&vs, vid);
    
    igraph_degree(graph1, &degree, vs, IGRAPH_ALL, false);
    int res = VECTOR(degree)[0];
    igraph_vector_destroy(&degree);
    igraph_vs_destroy(&vs);
    return res;
}
