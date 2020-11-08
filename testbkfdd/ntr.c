/**
  @file

  @ingroup testbkfdd

  @brief A very simple reachability analysis program.

  @author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from ntr.c
	
	@Modification and Extension details
		1. Add Ntr_buildBKFDDs to build BKFDDs and KFDDs.
		2. Delete some unneeded functions.
		3. Add fix_Canonicity to fix canonicity after changing expansions.
		4. Enable choose better expns for DD during building if MODE_SD actived.

		5. 2020-09-16: remove chooseSD, move it to bkfddBuild.c
======================================================================

**********************************************************************
	@copyright@parblock
  Copyright (c) 1995-2015, Regents of the University of Colorado

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  Neither the name of the University of Colorado nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.
  @endparblock
**********************************************************************

*/

#include "cuddInt.h"
#include "ntr.h"
#include "bkfddInt.h"
#include "bkfdd_bnet.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define NTR_MAX_DEP_SIZE 20

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void ntrInitializeCount (BnetNetwork *net, NtrOptions *option);
static void ntrCountDFS (BnetNetwork *net, BnetNode *node);

/*****************************************************************************
	@NOTE
	A safe way to introduce different expansion types during building is applying
	chooseSD3_restricted, chooseSD6_restricted after finishing a output.
*****************************************************************************/

/**
  @brief Builds BKFDDs for a network outputs and next state functions.

  @details The method is really brain-dead, but it is very simple.
  Some inputs to the network may be shared with another network whose
  DDs have already been built.  In this case we want to share the DDs
  as well.

  @return 1 in case of success; 0 otherwise.

  @sideeffect the dd fields of the network nodes are modified. Uses the
  count fields of the nodes.

*/
int
Ntr_buildBKFDDs(
  BnetNetwork * net /**< network for which DDs are to be built */,
  DdManager * dd /**< %DD manager */,
  NtrOptions * option /**< option structure */,
  BnetNetwork * net2 /**< companion network with which inputs may be shared */)
{
	int result;
	int i;
	BnetNode *node;

	/* If some inputs or present state variables are shared with
	** another network, we initialize their BDDs from that network.
	*/
	assert(net2 == NULL);

	/* First assign variables to inputs if the order is provided.
	** (Either in the .blif file or in an order file.)
	*/
	if (option->ordering == PI_PS_FROM_FILE) {
		/* Follow order given in input file. First primary inputs
		** and then present state variables.
		*/
		for (i = 0; i < net->npis; i++) {
			if (!st_lookup(net->hash,net->inputs[i],(void **)&node)) {
				return(0);
			}
			result = Bnet_BuildNodeBKFDD(dd,node,net,net->hash,
			option->locGlob,option->nodrop);
			if (result == 0) return(0);
		}
		for (i = 0; i < net->nlatches; i++) {
			if (!st_lookup(net->hash,net->latches[i][1],(void **)&node)) {
				return(0);
			}
			result = Bnet_BuildNodeBKFDD(dd,node,net,net->hash,
			option->locGlob,option->nodrop);
			if (result == 0) return(0);
		}
	} else if (option->ordering == PI_PS_GIVEN) {
		printf("This is unimplemented in BKFDD\n");
		assert(0);
		result = Bnet_ReadOrder(dd,option->orderPiPs,net,option->locGlob,
		option->nodrop);
		if (result == 0) return(0);
	} else {
		result = Bnet_DfsVariableOrder(dd,net);
		if (result == 0) return(0);
	}
	/* At this point the BDDs of all primary inputs and present state
	** variables have been built. */

	/* option->locGlob == BNET_GLOBAL_DD */
	/* Create BDDs with DFS from the primary outputs and the next
	** state functions. If the inputs had not been ordered yet,
	** this would result in a DFS order for the variables.
	*/
	ntrInitializeCount(net,option);
	if (option->node != NULL &&
	option->closestCube == FALSE && option->dontcares == FALSE) {
		if (!st_lookup(net->hash,option->node,(void **)&node)) {
			return(0);
		}
		result = Bnet_BuildNodeBKFDD(dd,node,net,net->hash,BNET_GLOBAL_DD,
		option->nodrop);
		if (result == 0) return(0);
	} else {
		if (option->stateOnly == FALSE) {
			for (i = 0; i < net->npos; i++) {
				if (!st_lookup(net->hash,net->outputs[i],(void **)&node)) {
					continue;
				}
				result = Bnet_BuildNodeBKFDD(dd,node,net,net->hash,
				BNET_GLOBAL_DD,option->nodrop);
				if (result == 0) return(0);
				
				if (dd->autoDyn && dd->bkfddMode == MODE_SD) {
					/* SD mode, all expansions are introduced during building. */
					if ((int)dd->keys > dd->choose_threshold) {
						/* Do GC before choose better expansions. */
						cuddCacheFlush(dd);
						cuddGarbageCollect(dd,0);
						if (dd->autoMethod == BKFDD_GROUP_SIFT ||
								dd->autoMethod == BKFDD_SYMM_SIFT ||
								dd->autoMethod == BKFDD_GROUP_SIFT_NMEG) {
							if (!chooseSD6(dd)) return(0);
							/* once introduce pD expansions, we
								need to fix canonicity of DD nodes*/
							if (fix_Canonicity(dd, net, dd->size-1) == 0) {
								fprintf(dd->err,"fix canonicity failed\n");
								return(0);
							}
							if (!chooseSD3(dd)) return(0);
							/* once introduce pD expansions, we
								need to fix canonicity of DD nodes*/
							if (fix_Canonicity(dd, net, dd->size-1) == 0) {
								fprintf(dd->err,"fix canonicity failed\n");
								return(0);
							}
						} else if (dd->autoMethod == KFDD_GROUP_SIFT ||
											dd->autoMethod == KFDD_SYMM_SIFT){
							if (!chooseSD3(dd)) return(0);
							if (fix_Canonicity(dd, net, dd->size-1) == 0) {
								fprintf(dd->err,"fix canonicity failed\n");
								return(0);
							}
						}
						Cudd_ReduceHeap(dd,dd->autoMethod,1);
						dd->choose_threshold = (int)(dd->keys * 1.8);
					}
				}
				
				if (option->progress)  {
					(void) fprintf(stdout,"%s\n",node->name);
				}
			}
		}
		for (i = 0; i < net->nlatches; i++) {
			if (!st_lookup(net->hash,net->latches[i][0],(void **)&node)) {
				continue;
			}
			result = Bnet_BuildNodeBKFDD(dd,node,net,net->hash,BNET_GLOBAL_DD,
			option->nodrop);
			if (result == 0) return(0);
#if 0
			if (dd->autoDyn && dd->bkfddMode == MODE_SD) {
				/* SD mode, all expansions are introduced during building. */
				if ((int)dd->keys > dd->choose_threshold) {
					/* Do GC before choose better expansions. */
					cuddCacheFlush(dd);
					cuddGarbageCollect(dd,0);
					if (dd->autoMethod == BKFDD_GROUP_SIFT ||
							dd->autoMethod == BKFDD_SYMM_SIFT ||
							dd->autoMethod == BKFDD_GROUP_SIFT_NMEG) {
						if (!chooseSD6(dd)) return(0);
						/* once introduce pD expansions, we
							need to fix canonicity of DD nodes*/
						if (fix_Canonicity(dd, net, dd->size-1) == 0) {
							fprintf(dd->err,"fix canonicity failed\n");
							return(0);
						}
						if (!chooseSD3(dd)) return(0);
						/* once introduce pD expansions, we
							need to fix canonicity of DD nodes*/
						if (fix_Canonicity(dd, net, dd->size-1) == 0) {
							fprintf(dd->err,"fix canonicity failed\n");
							return(0);
						}
					} else if (dd->autoMethod == KFDD_GROUP_SIFT ||
										dd->autoMethod == KFDD_SYMM_SIFT){
						if (!chooseSD3(dd)) return(0);
						if (fix_Canonicity(dd, net, dd->size-1) == 0) {
							fprintf(dd->err,"fix canonicity failed\n");
							return(0);
						}
					}
					Cudd_ReduceHeap(dd,dd->autoMethod,1);
					dd->choose_threshold = (int)(dd->keys * 1.8);
				}
			}
#endif
			if (option->progress)  {
				(void) fprintf(stdout,"%s\n",node->name);
			}
		}
	}
	/* Make sure all inputs have a DD and dereference the DDs of
	** the nodes that are not reachable from the outputs.
	*/
	for (i = 0; i < net->npis; i++) {
		if (!st_lookup(net->hash,net->inputs[i],(void **)&node)) {
			return(0);
		}
		result = Bnet_BuildNodeBKFDD(dd,node,net,net->hash,BNET_GLOBAL_DD,
		option->nodrop);
		if (result == 0) return(0);		
		if (node->count == -1) Cudd_RecursiveDeref(dd,node->dd);
	}
	for (i = 0; i < net->nlatches; i++) {
		if (!st_lookup(net->hash,net->latches[i][1],(void **)&node)) {
			return(0);
		}
		result = Bnet_BuildNodeBKFDD(dd,node,net,net->hash,BNET_GLOBAL_DD,
		option->nodrop);
		if (result == 0) return(0);
		if (node->count == -1) Cudd_RecursiveDeref(dd,node->dd);
	}

	/* Dispose of the BKFDDs of the internal nodes if they have not
	** been dropped already.
	*/
	if (option->nodrop == TRUE) {
		for (node = net->nodes; node != NULL; node = node->next) {
			if (node->dd != NULL && node->count != -1 &&
				(node->type == BNET_INTERNAL_NODE ||
				node->type == BNET_INPUT_NODE ||
				node->type == BNET_PRESENT_STATE_NODE)) {
				Cudd_RecursiveDeref(dd,node->dd);
				if (node->type == BNET_INTERNAL_NODE) node->dd = NULL;
			}
		}
	}

	return(1);

} /* end of Ntr_buildBKFDDs */


/**
  @brief Initializes the count fields used to drop DDs.

  @details Before actually building the BDDs, we perform a DFS from
  the outputs to initialize the count fields of the nodes.  The
  initial value of the count field will normally coincide with the
  fanout of the node.  However, if there are nodes with no path to any
  primary output or next state variable, then the initial value of
  count for some nodes will be less than the fanout. For primary
  outputs and next state functions we add 1, so that we will never try
  to free their DDs. The count fields of the nodes that are not
  reachable from the outputs are set to -1.

  @sideeffect Changes the count fields of the network nodes. Uses the
  visited fields.

*/
static void
ntrInitializeCount(
  BnetNetwork * net,
  NtrOptions * option)
{
	BnetNode *node;
	int i;

	if (option->node != NULL &&
	option->closestCube == FALSE && option->dontcares == FALSE) {
	if (!st_lookup(net->hash,option->node,(void **)&node)) {
	(void) fprintf(stdout, "Warning: node %s not found!\n",
	option->node);
	} else {
	ntrCountDFS(net,node);
	node->count++;
	}
	} else {
	if (option->stateOnly == FALSE) {
	for (i = 0; i < net->npos; i++) {
	if (!st_lookup(net->hash,net->outputs[i],(void **)&node)) {
	(void) fprintf(stdout,
	"Warning: output %s is not driven!\n",
	net->outputs[i]);
	continue;
	}
	ntrCountDFS(net,node);
	node->count++;
	}
	}
	for (i = 0; i < net->nlatches; i++) {
	if (!st_lookup(net->hash,net->latches[i][0],(void **)&node)) {
	(void) fprintf(stdout,
	"Warning: latch input %s is not driven!\n",
	net->outputs[i]);
	continue;
	}
	ntrCountDFS(net,node);
	node->count++;
	}
	}

	/* Clear visited flags. */
	node = net->nodes;
	while (node != NULL) {
	if (node->visited == 0) {
	node->count = -1;
	} else {
	node->visited = 0;
	}
	node = node->next;
	}

} /* end of ntrInitializeCount */


/**
  @brief Does a DFS from a node setting the count field.

  @sideeffect Changes the count and visited fields of the nodes it
  visits.

  @see ntrLevelDFS

*/
static void
ntrCountDFS(
  BnetNetwork * net,
  BnetNode * node)
{
	int i;
	BnetNode *auxnd;

	node->count++;

	if (node->visited == 1) {
	return;
	}

	node->visited = 1;

	for (i = 0; i < node->ninp; i++) {
	if (!st_lookup(net->hash, node->inputs[i], (void **)&auxnd)) {
	exit(2);
	}
	ntrCountDFS(net,auxnd);
	}

} /* end of ntrCountDFS */
