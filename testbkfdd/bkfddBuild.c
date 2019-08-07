/**
  @file

  @ingroup testbkfdd

  @brief Functions to build BKFDD from Boolean network.

	@author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	All functions are originate from bnet.c
	
	@Modification and Extension details
		1. Modify buildExorBDD, buildMuxBDD, Bnet_BuildNodeBDD, Bnet_bddArrayDump
			and Bnet_bddDump to compatible with BKFDDs.
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

#include "bkfddInt.h"
#include "bnet.h"

static int buildExorBKFDD (DdManager *dd, BnetNode *nd, BnetNetwork * net, st_table *hash, int params, int nodrop);
static int buildMuxBKFDD (DdManager * dd, BnetNode * nd, BnetNetwork * net, st_table * hash, int  params, int  nodrop);

/*********************************************************************
	@NOTE:
	Apply chooseSD3, chooseSD6 in Bnet_BuildNodeBKFDD, buildExorBKFDD, buildMuxBKFDD
	may make resulting DDs incorrect. Because intermediate results won't be stored
	in BnetNetwork, fixing canonicity after changing expansions will cause
	intermediate results incorrect(lose information of complemented edges).
*********************************************************************/

/**
  @brief Builds the %BKFDD for the function of a node.

  @details Builds the %BKFDD for the function of a node and stores a
  pointer to it in the dd field of the node itself. The reference count
  of the %BKFDD is incremented. If params is BNET_LOCAL_DD, then the %BKFDD is
  built in terms of the local inputs to the node; otherwise, if params
  is BNET_GLOBAL_DD, the %BKFDD is built in terms of the network primary
  inputs. To build the global %BKFDD of a node, the BKFDDs for its local
  inputs must exist. If that is not the case, Bnet_BuildNodeBKFDD
  recursively builds them. Likewise, to create the local %BKFDD for a node,
  the local inputs must have variables assigned to them. If that is not
  the case, Bnet_BuildNodeBKFDD recursively assigns variables to nodes.

  @return 1 in case of success; 0 otherwise.

  @sideeffect Sets the dd field of the node.

*/
int
Bnet_BuildNodeBKFDD(
  DdManager * dd /**< %DD manager */,
  BnetNode * nd /**< node of the boolean network */,
	BnetNetwork * net /**< fixing canonicity purpose */,
  st_table * hash /**< symbol table of the boolean network */,
  int  params /**< type of %DD to be built */,
  int  nodrop /**< retain the intermediate node DDs until the end */)
{
	DdNode *func;
	BnetNode *auxnd;
	DdNode *tmp;
	DdNode *prod, *var;
	BnetTabline *line;
	int i;

	if (nd->dd != NULL) return(1);

	if (nd->type == BNET_CONSTANT_NODE) {
		if (nd->f == NULL) { /* constant 0 */
			func = Cudd_ReadLogicZero(dd);
		} else { /* either constant depending on the polarity */
			func = Cudd_ReadOne(dd);
		}
		Cudd_Ref(func);
	} else if (nd->type == BNET_INPUT_NODE ||
		nd->type == BNET_PRESENT_STATE_NODE) {
		if (nd->active == TRUE) { /* a variable is already associated: use it */
			func = Cudd_ReadVars(dd,nd->var);
			if (func == NULL) goto failure;
		} else { /* no variable associated: get a new one */
			func = Cudd_bddNewVar(dd);
			if (func == NULL) goto failure;
			nd->var = Cudd_Regular(func)->index;
			nd->active = TRUE;
		}
		Cudd_Ref(func);
	} else if (buildExorBKFDD(dd,nd,net,hash,params,nodrop)) {
		func = nd->dd;
	} else if (buildMuxBKFDD(dd,nd,net,hash,params,nodrop)) {
		func = nd->dd;
	} else { /* type == BNET_INTERNAL_NODE or BNET_OUTPUT_NODE */
		/* Initialize the sum to logical 0. */
		func = Cudd_ReadLogicZero(dd);
		Cudd_Ref(func);

		/* Build a term for each line of the table and add it to the
		** accumulator (func).
		*/
		line = nd->f;
		while (line != NULL) {
#ifdef BNET_DEBUG
			(void) fprintf(stdout,"line = %s\n", line->values);
#endif
			/* Initialize the product to logical 1. */
			prod = Cudd_ReadOne(dd);
			Cudd_Ref(prod);
			/* Scan the table line. */
			for (i = 0; i < nd->ninp; i++) {
				if (line->values[i] == '-') continue;
				if (!st_lookup(hash,nd->inputs[i],(void **)&auxnd)) {
					goto failure;
				}
				if (auxnd->dd == NULL) {
					if (!Bnet_BuildNodeBKFDD(dd,auxnd,net,hash,params,nodrop)) {
						goto failure;
					}
				}
				if (line->values[i] == '1') {
					var = auxnd->dd;
				} else { /* line->values[i] == '0' */
					var = Cudd_Not(auxnd->dd);
				}
				tmp = Bkfdd_And(dd,prod,var);
				if (tmp == NULL) goto failure;
				Cudd_Ref(tmp);
				Cudd_IterDerefBdd(dd,prod);
				prod = tmp;
			}
			tmp = Bkfdd_Or(dd,func,prod);
			if (tmp == NULL) goto failure;
			Cudd_Ref(tmp);
			Cudd_IterDerefBdd(dd,func);
			Cudd_IterDerefBdd(dd,prod);
			func = tmp;
			line = line->next;
		}
	}
	if (nd->polarity == 1) {
		nd->dd = Cudd_Not(func);
	} else {
		nd->dd = func;
	}

	if (params == BNET_GLOBAL_DD && nodrop == FALSE) {
		/* Decrease counters for all faninis.
		** When count reaches 0, the DD is freed.
		*/
		for (i = 0; i < nd->ninp; i++) {
			if (!st_lookup(hash,nd->inputs[i],(void **)&auxnd)) {
					goto failure;
			}
			auxnd->count--;
			if (auxnd->count == 0) {
				Cudd_IterDerefBdd(dd,auxnd->dd);
				if (auxnd->type == BNET_INTERNAL_NODE ||
				auxnd->type == BNET_CONSTANT_NODE) auxnd->dd = NULL;
			}
		}
	}
	return(1);

failure:	
	/* Here we should clean up the mess. */
	return(0);

} /* end of Bnet_BuildNodeBKFDD */


/**
  @brief Builds %BKFDD for a XOR function.

  @details Checks whether a function is a XOR with 2 or 3 inputs. If so,
  it builds the %BKFDD.

  @return 1 if the %BKFDD has been built; 0 otherwise.

  @sideeffect None

*/
static int
buildExorBKFDD(
  DdManager * dd,
  BnetNode * nd,
	BnetNetwork * net,
  st_table * hash,
  int  params,
  int  nodrop)
{
	int check[8];
	int i;
	int nlines;
	BnetTabline *line;
	DdNode *func, *var, *tmp;
	BnetNode *auxnd;

	if (nd->ninp < 2 || nd->ninp > 3) return(0);

	nlines = 1 << (nd->ninp - 1);
	for (i = 0; i < 8; i++) check[i] = 0;
	line = nd->f;
	while (line != NULL) {
		int num = 0;
		int count = 0;
		nlines--;
		for (i = 0; i < nd->ninp; i++) {
			num <<= 1;
			if (line->values[i] == '-') {
				return(0);
			} else if (line->values[i] == '1') {
				count++;
				num++;
			}
		}
		if ((count & 1) == 0) return(0);
		if (check[num]) return(0);
		line = line->next;
	}
	if (nlines != 0) return(0);

	/* Initialize the exclusive sum to logical 0. */
	func = Cudd_ReadLogicZero(dd);
	Cudd_Ref(func);

	/* Scan the inputs. */
	for (i = 0; i < nd->ninp; i++) {
		if (!st_lookup(hash, nd->inputs[i], (void **) &auxnd)) {
			goto failure;
		}
		if (auxnd->dd == NULL) {
			if (!Bnet_BuildNodeBKFDD(dd,auxnd,net,hash,params,nodrop)) {
				goto failure;
			}
		}
		var = auxnd->dd;
		tmp = Bkfdd_Xor(dd,func,var);
		if (tmp == NULL) goto failure;
		Cudd_Ref(tmp);
		Cudd_IterDerefBdd(dd,func);
		func = tmp;
	}
	nd->dd = func;

	return(1);
failure:
	return(0);

} /* end of buildExorBKFDD */


/**
  @brief Builds %BKFDD for a multiplexer.

  @details Checks whether a function is a 2-to-1 multiplexer. If so,
  it builds the %BKFDD.

  @return 1 if the %BKFDD has been built; 0 otherwise.

  @sideeffect None

*/
static int
buildMuxBKFDD(
  DdManager * dd,
  BnetNode * nd,
	BnetNetwork * net,
  st_table * hash,
  int  params,
  int  nodrop)
{
	BnetTabline *line;
	char *values[2];
	int mux[2] = {0, 0};
	int phase[2] = {0, 0};
	int j;
	int nlines = 0;
	int controlC = -1;
	int controlR = -1;
	DdNode *func, *f, *g, *h;
	BnetNode *auxnd;

	if (nd->ninp != 3 || nd->f == NULL) return(0);

	for (line = nd->f; line != NULL; line = line->next) {
		int dc = 0;
		if (nlines > 1) return(0);
		values[nlines] = line->values;
		for (j = 0; j < 3; j++) {
			if (values[nlines][j] == '-') {
				if (dc) return(0);
				dc = 1;
			}
		}
		if (!dc) return(0);
		nlines++;
	}
	if (nlines != 2) return(0);
	/* At this point we know we have:
	**   3 inputs
	**   2 lines
	**   1 dash in each line
	** If the two dashes are not in the same column, then there is
	** exaclty one column without dashes: the control column.
	*/
	for (j = 0; j < 3; j++) {
		if (values[0][j] == '-' && values[1][j] == '-') return(0);
		if (values[0][j] != '-' && values[1][j] != '-') {
			if (values[0][j] == values[1][j]) return(0);
			controlC = j;
			controlR = values[0][j] == '0';
		}
	}
	assert(controlC != -1 && controlR != -1);
	/* At this point we know that there is indeed no column with two
	** dashes. The control column has been identified, and we know that
	** its two elelments are different. */
	for (j = 0; j < 3; j++) {
		if (j == controlC) continue;
		if (values[controlR][j] == '1') {
			mux[0] = j;
			phase[0] = 0;
		} else if (values[controlR][j] == '0') {
			mux[0] = j;
			phase[0] = 1;
		} else if (values[1-controlR][j] == '1') {
			mux[1] = j;
			phase[1] = 0;
		} else if (values[1-controlR][j] == '0') {
			mux[1] = j;
			phase[1] = 1;
		}
	}

	/* Get the inputs. */
	if (!st_lookup(hash, nd->inputs[controlC], (void **) &auxnd)) {
		goto failure;
	}
	if (auxnd->dd == NULL) {
		if (!Bnet_BuildNodeBKFDD(dd,auxnd,net,hash,params,nodrop)) {
			goto failure;
		}
	}
	f = auxnd->dd;
	if (!st_lookup(hash, nd->inputs[mux[0]], (void **) &auxnd)) {
		goto failure;
	}
	if (auxnd->dd == NULL) {
		if (!Bnet_BuildNodeBKFDD(dd,auxnd,net,hash,params,nodrop)) {
			goto failure;
		}
	}
	g = auxnd->dd;
	g = Cudd_NotCond(g,phase[0]);
	if (!st_lookup(hash, nd->inputs[mux[1]], (void **) &auxnd)) {
		goto failure;
	}
	if (auxnd->dd == NULL) {
		if (!Bnet_BuildNodeBKFDD(dd,auxnd,net,hash,params,nodrop)) {
			goto failure;
		}
	}
	h = auxnd->dd;
	h = Cudd_NotCond(h,phase[1]);
	func = Bkfdd_Ite(dd,f,g,h);
	if (func == NULL) goto failure;
	Cudd_Ref(func);
	nd->dd = func;

	return(1);
failure:
	return(0);

} /* end of buildMuxBKFDD */


/** 
	@brief Fix canonicity
	
	@details Fix canonicity of nodes after expansion change.
	Make sure there is no dead node.
	
*/
int
fix_Canonicity(
	DdManager * dd /**< %DD manager */,
  BnetNetwork * network /**< network whose BKFDDs should be dumped */)
{
	int i, ii;
	DdNode *one = DD_ONE(dd);
	BnetNode *bnode;
	DdNode *p, *next, *nodechain, *t, *e, *tmp;
	unsigned int slots, posn, k;
	bnode = NULL;
	p = next = nodechain = t = e = tmp = NULL;
	DdNodePtr *previousP = NULL;
	DdNode *sentinel = &(dd->sentinel);
	assert(isCla(dd->expansion[dd->size-1]));

	/* traverse all upper level nodes, move CEs，
		if T of cuddT is complemented, complement cuddT,
		if T of cuddE is complemented, complement cuddE. */
	for (i = dd->size-1; i >= 0; i --) {
		DdNodePtr *nodelist = dd->subtables[i].nodelist;
		slots = dd->subtables[i].slots;
		for (k = 0; k < slots; k ++) {
			p = nodelist[k];
			while (p != sentinel) {
				next = p->next;
				t = cuddT(p);
				e = cuddE(p);
				/* T and E may complemented, NOTE that 
					pointer passed to cuddT() and cuddE() must be regular */
				if (Cudd_Regular(t) != one) {
					if (Cudd_IsComplement(cuddT(Cudd_Regular(t)))) {
						// violate low-regular principle
						cuddT(p) = Cudd_Not(t);
					}
				}
				if (Cudd_Regular(e) != one) {
					if (Cudd_IsComplement(cuddT(Cudd_Regular(e)))) {
						// violate low-regular principle
						cuddE(p) = Cudd_Not(e);
					}
				}
				p = next;
			}
		}
	}
	/* fix canonicity of variable array */
	for (ii = 0; ii < dd->size; ii ++) {
		p = Cudd_Regular(dd->vars[ii]);
		if (Cudd_IsComplement(cuddT(p))) {
			dd->vars[ii] = Cudd_Not(dd->vars[ii]);
		}
	}
	/* fix canonicity of network nodes */
	bnode = network->nodes;
	while (bnode != NULL) {
		// bnode->dd may be complemented
		p = Cudd_Regular(bnode->dd);
		if (p != NULL && p != one) {
			if (Cudd_IsComplement(cuddT(p))) {
				bnode->dd = Cudd_Not(bnode->dd);
			}
		}
		bnode = bnode->next;
	}

	/* make upper nodes canonical,
		if T of node is complemented, remove complemented mark,
		and rehash subtables. */
	for (i = dd->size-1; i >= 0; i --) {
		DdNodePtr *list = dd->subtables[i].nodelist;
		slots = dd->subtables[i].slots;
		int shift = dd->subtables[i].shift;
		int dec = dd->expansion[i];
		/* Empty current nodelist, put them to nodechain. */
		for (k = 0; k < slots; k ++) {
			p = list[k];
			while (p != sentinel) {
				next = p->next;
				p->next = nodechain;
				nodechain = p;
				p = next;
			} /* while there are elements in the collision chain */
		} /* for each slot of the subtable */
		for (k = 0; k < slots; k ++) {
			list[k] = sentinel;
		}
		while (nodechain != NULL) {
			next = nodechain->next;
			t = cuddT(nodechain);
			e = cuddE(nodechain);
			if (Cudd_IsComplement(t)) {
				cuddT(nodechain) = Cudd_Not(t);
				if (isShan(dec)) {
					cuddE(nodechain) = Cudd_Not(e);
				}
			}
			t = cuddT(nodechain);
			e = cuddE(nodechain);
			/* Re-compute hash value, and re-insert to subtable. */
			posn = ddHash(t, e, shift);
			previousP = &(list[posn]);
			tmp = *previousP;
			while (t < cuddT(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			while (t == cuddT(tmp) && e < cuddE(tmp)) {
				previousP = &(tmp->next);
				tmp = *previousP;
			}
			nodechain->next = *previousP;
			*previousP = nodechain;
			nodechain = next;
		}
	}

	return(1);
} /* End of fix_Canonicity */


/**
  @brief Writes the network BKFDDs to a file in blif format.

  @details If "-" is passed as file name, the BKFDDs are dumped to the
  standard output.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
int
Bnet_bkfddDump(
  DdManager * dd /**< %DD manager */,
  BnetNetwork * network /**< network whose BKFDDs should be dumped */,
  char * dfile /**< file name */)
{
	int noutputs;
	FILE *dfp = NULL;
	DdNode **outputs = NULL;
	char **inames = NULL;
	char **onames = NULL;
	BnetNode *bnode;
	int i;
	int retval = 0; /* 0 -> failure; 1 -> success */

	/* Open dump file. */
	if (strcmp(dfile, "-") == 0) {
		dfp = stdout;
	} else {
		dfp = fopen(dfile,"w");
	}
	if (dfp == NULL) goto endgame;

	/* Initialize data structures. */
	noutputs = network->noutputs;
	outputs = ALLOC(DdNode *,noutputs);
	if (outputs == NULL) goto endgame;
	onames = ALLOC(char *,noutputs);
	if (onames == NULL) goto endgame;
	inames = ALLOC(char *,Cudd_ReadSize(dd));
	if (inames == NULL) goto endgame;

	/* Find outputs and their names. */
	for (i = 0; i < network->nlatches; i++) {
		onames[i] = network->latches[i][0];
		if (!st_lookup(network->hash,network->latches[i][0],(void **)&bnode)) {
			goto endgame;
		}
		outputs[i] = bnode->dd;
	}
	for (i = 0; i < network->npos; i++) {
		onames[i + network->nlatches] = network->outputs[i];
		if (!st_lookup(network->hash,network->outputs[i],(void **)&bnode)) {
			goto endgame;
		}
		outputs[i + network->nlatches] = bnode->dd;
	}

	/* Find the input names.
		inames[variable_index] = variable_name. */
	for (i = 0; i < network->ninputs; i++) {
		if (!st_lookup(network->hash,network->inputs[i],(void **)&bnode)) {
			goto endgame;
		}
		inames[bnode->var] = network->inputs[i];
	}
	for (i = 0; i < network->nlatches; i++) {
		if (!st_lookup(network->hash,network->latches[i][1],(void **)&bnode)) {
			goto endgame;
		}
		inames[bnode->var] = network->latches[i][1];
	}

	retval = Bkfdd_DumpBlif(dd,noutputs,outputs,
	(char const * const *) inames,
	(char const * const *) onames,
	network->name,dfp);	

endgame:
	if (dfp != stdout && dfp != NULL) {
		if (fclose(dfp) == EOF) retval = 0;
	}
	if (outputs != NULL) FREE(outputs);
	if (onames  != NULL) FREE(onames);
	if (inames  != NULL) FREE(inames);

	return(retval);

} /* end of Bnet_bkfddDump */


/**
  @brief Writes an array of BKFDDs to a file in blif format.

  @details The BKFDDs and their names are passed as arguments.  The
  inputs and their names are taken from the network. If "-" is passed
  as file name, the BKFDDs are dumped to the standard output.

  @return 1 in case of success; 0 otherwise.

  @sideeffect None

*/
int
Bnet_bkfddArrayDump(
  DdManager * dd /**< %DD manager */,
  BnetNetwork * network /**< network whose BKFDDs should be dumped */,
	char * dfile /**< file name */,
  DdNode ** outputs /**< BKFDDs to be dumped */,
  char ** onames /**< names of the BKFDDs to be dumped */,
  int  noutputs /**< number of BKFDDs to be dumped */)
{
	FILE *dfp = NULL;
	char **inames = NULL;
	BnetNode *bnode;
	int i;
	int retval = 0; /* 0 -> failure; 1 -> success */

	/* Open dump file. */
	if (strcmp(dfile, "-") == 0) {
		dfp = stdout;
	} else {
		dfp = fopen(dfile,"w");
	}
	if (dfp == NULL) goto endgame;

	/* Initialize data structures. */
	inames = ALLOC(char *,Cudd_ReadSize(dd));
	if (inames == NULL) goto endgame;
	for (i = 0; i < Cudd_ReadSize(dd); i++) {
		inames[i] = NULL;
	}

	/* Find the input names. */
	for (i = 0; i < network->ninputs; i++) {
		if (!st_lookup(network->hash,network->inputs[i],(void **)&bnode)) {
			goto endgame;
		}
		inames[bnode->var] = network->inputs[i];
	}
	for (i = 0; i < network->nlatches; i++) {
		if (!st_lookup(network->hash,network->latches[i][1],(void **)&bnode)) {
			goto endgame;
		}
		inames[bnode->var] = network->latches[i][1];
	}

	retval = Bkfdd_DumpBlif(dd,noutputs,outputs,
	(char const * const *) inames,
	(char const * const *) onames,
	network->name,dfp);

endgame:
	if (dfp != stdout && dfp != NULL) {
		if (fclose(dfp) == EOF) retval = 0;
	}
	if (inames  != NULL) FREE(inames);

	return(retval);

} /* end of Bnet_bkfddArrayDump */
