/**
  @file 

  @ingroup testbkfdd

  @brief Simple-minded package to read a blif file.

	@author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	@Modification and Extension details
		1. Add declarations of functions in bkfddBuild.c, surrounded by
	"Xuanxiang Huang" or "BKFDD"
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

#ifndef BKFDD_BNET
#define BKFDD_BNET

/*---------------------------------------------------------------------------*/
/* Nested includes                                                           */
/*---------------------------------------------------------------------------*/

#include "util.h"
#include "st.h"
#include "cudd.h"
#include "bnet.h"

#ifdef __cplusplus
extern "C" {
#endif

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

extern int changeExpnBetweenSND_bnet(DdManager * dd, int level, BnetNetwork * network);
extern int changeExpnBetweenNDPD_bnet(DdManager * dd, int level, BnetNetwork * network);
extern int changeExpnPDtoS_bnet(DdManager * dd, int level, BnetNetwork * network);
extern int changeExpnStoPD_bnet(DdManager * dd, int level, BnetNetwork * network);
extern int changeExpnBetweenBiCla_bnet(DdManager * dd,	int level, BnetNetwork * network);
extern int chooseSD3_restricted_bnet(DdManager * table, BnetNetwork * network);
extern int chooseSD6_restricted_bnet(DdManager * table, BnetNetwork * network);
extern int bkfdd_reorder_bnet(DdManager * table,Cudd_ReorderingType heuristic,int minsize,BnetNetwork *net);
extern int odtSifting_bnet(DdManager * table,int lower,int upper, BnetNetwork * network);
extern int Bnet_BuildNodeBKFDD(DdManager *dd, BnetNode *nd, BnetNetwork * net, st_table *hash, int params, int nodrop);
extern int fix_Canonicity(DdManager * dd, BnetNetwork * network, int level);
extern DdNode * fix_Canonicity_node(DdManager * dd, DdNode *node);
extern int checkBkfddVar(DdManager * dd);
// dump BKFDD into file
extern int Bnet_bkfddDump(DdManager * dd, BnetNetwork * network, char * dfile);
extern int Bnet_bkfddArrayDump(DdManager * dd, BnetNetwork * network, char * dfile, DdNode ** outputs, char ** onames, int noutputs);

#ifdef __cplusplus
} /* end of extern "C" */
#endif

#endif /* BKFDD_BNET */
