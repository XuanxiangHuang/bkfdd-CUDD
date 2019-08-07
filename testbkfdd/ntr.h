/**
  @file 

  @ingroup testbkfdd

  @brief Simple-minded package to do traversal.

  @author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================	
	@Modification and Extension details
		1. Add declarations of Ntr_buildBKFDDs.
		2. Add argument davioExist, to control how many non-Shannon expansions
				allowed to exist in chooseBetter**DD procedures.
		3. Add argument chooseLowBound, to control when to exist chooseBetter**DD
				procedures if size of DD has reduced X percent.
		4. Add argument chooseNew, to control when a new expansion can be accepted
				in chooseBetter**DD procedures.
		5. Add argument chooseDav, to control when a non-Shannon expansions can
				be accepted in chooseBetter**DD procedures.
		6. Add argument chooseFail, to control when to exist chooseBetter**DD
				procedures if changing expansions of current BKFDDs cannot satisfy
				above restrictions.
		7. Add bkfdd mode option.
		surrounded by	"Xuanxiang Huang" or "BKFDD"
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

#ifndef _NTR
#define _NTR

/*---------------------------------------------------------------------------*/
/* Nested includes                                                           */
/*---------------------------------------------------------------------------*/

#include "dddmp.h"
#include "bnet.h"

#ifdef __cplusplus
extern "C" {
#endif

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define PI_PS_FROM_FILE	0
#define PI_PS_DFS	1
#define PI_PS_GIVEN	2

#define NTR_IMAGE_MONO 0
#define NTR_IMAGE_PART 1
#define NTR_IMAGE_CLIP 2
#define NTR_IMAGE_DEPEND 3

#define NTR_UNDER_APPROX 0
#define NTR_OVER_APPROX 1

#define NTR_FROM_NEW 0
#define NTR_FROM_REACHED 1
#define NTR_FROM_RESTRICT 2
#define NTR_FROM_COMPACT 3
#define NTR_FROM_SQUEEZE 4
#define NTR_FROM_UNDERAPPROX 5
#define NTR_FROM_OVERAPPROX 6

#define NTR_GROUP_NONE 0
#define NTR_GROUP_DEFAULT 1
#define NTR_GROUP_FIXED 2

#define NTR_SHORT_NONE 0
#define NTR_SHORT_BELLMAN 1
#define NTR_SHORT_FLOYD 2
#define NTR_SHORT_SQUARE 3

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/**
   @brief Options for nanotrav.
*/
typedef	struct	NtrOptions {
	long	initialTime;	/**< this is here for convenience */
	int		verify;		/**< read two networks and compare them */
	char	*file1;		/**< first network file name */
	char	*file2;		/**< second network file name */
	int		second;		/**< a second network is given */
	int		traverse;	/**< do reachability analysis */
	int		depend;		/**< do latch dependence analysis */
	int		image;		/**< monolithic, partitioned, or clip */
	double	imageClip;	/**< clipping depth in image computation */
	int		approx;		/**< under or over approximation */
	int		threshold;	/**< approximation threshold */
	int		from;		/**< method to compute from states */
	int		groupnsps;	/**< group present state and next state vars */
	int		closure;	/**< use transitive closure */
	double	closureClip;	/**< clipping depth in closure computation */
	int		envelope;	/**< compute outer envelope */
	int		scc;		/**< compute strongly connected components */
	int		zddtest;	/**< do zdd test */
	int		printcover;	/**< print ISOP covers when testing ZDDs */
	int		maxflow;	/**< compute maximum flow in network */
	int		shortPath;	/**< compute shortest paths in network */
	int		selectiveTrace;	/**< use selective trace in shortest paths */
	char	*sinkfile;	/**< file for externally provided sink node */
	int		partition;	/**< test McMillan conjunctive partitioning */
	int		char2vect;	/**< test char-to-vect decomposition */
	int		density;	/**< test density-related functions */
	double	quality;	/**< quality parameter for density functions */
	int		decomp;		/**< test decomposition functions */
	int		cofest;		/**< test cofactor estimation */
	double	clip;		/**< test clipping functions */
	int		dontcares;	/**< test equivalence and containment with DCs */
	int		closestCube;	/**< test Cudd_bddClosestCube */
	int		clauses;	/**< test extraction of two-literal clauses */
	int		noBuild;	/**< do not build BDDs; just echo order */
	int		stateOnly;	/**< ignore primary outputs */
	char	*node;		/**< only node for which to build %BDD */
	int		locGlob;	/**< build global or local BDDs */
	int		progress;	/**< report output names while building BDDs */
	int		cacheSize;	/**< computed table initial size */
	size_t	 maxMemory;	/**< target maximum memory */
	size_t	 maxMemHard;	/**< maximum allowed memory */
	unsigned int maxLive;	/**< maximum number of nodes */
	int		slots;		/**< unique subtable initial slots */
	int		ordering;	/**< FANIN DFS ... */
	char	*orderPiPs;	/**< file for externally provided order */
	Cudd_ReorderingType	reordering; /**< NONE RANDOM PIVOT SIFTING ... */
	int		autoDyn;	/**< ON OFF */
	Cudd_ReorderingType autoMethod; /**< RANDOM PIVOT SIFTING CONVERGE ... */
	char	*treefile;	/**< file name for variable tree */
	int		firstReorder;	/**< when to do first reordering */
	int		countDead;	/**< count dead nodes toward triggering
	reordering */
	int		maxGrowth;	/**< maximum growth during reordering (%) */
	Cudd_AggregationType groupcheck; /**< grouping function */
	int		arcviolation;   /**< percent violation of arcs in
	extended symmetry check */
	int		symmviolation;  /**< percent symm violation in
	extended symmetry check */
	int		recomb;		/**< recombination parameter for grouping */
	int		nodrop;		/**< don't drop intermediate BDDs ASAP */
	int		signatures;	/**< computation of signatures */
	int		gaOnOff;	/**< whether to run GA at the end */
	int		populationSize;	/**< population size for GA */
	int		numberXovers;	/**< number of crossovers for GA */
	int		bdddump;	/**< ON OFF */
	int		dumpFmt;	/**< 0 -> dot 1 -> blif 2 ->daVinci 3 -> DDcal
	** 4 -> factored form */
	char	*dumpfile;	/**< filename for dump */
	int		store;		/**< iteration at which to store Reached */
	char	*storefile;	/**< filename for storing Reached */
	int		load;		/**< load initial states from file */
	char	*loadfile;	/**< filename for loading states */
	int		verb;		/**< level of verbosity */
	int32_t	seed;		/**< seed for random number generator */
/** Xuanxiang Huang:BKFDD */
	/* Arguments in chooseBetter**DD procedures */
	int davioExist; /** choose better DDs */
	int chooseLowBound; /** lower bound of size in choose better DDs */
	int chooseNew;
	int chooseDav;
	int chooseFail;
	int bkfddMode;
/** Xuanxiang Huang:BKFDD */
} NtrOptions;

/**
   @brief Type of entry of NtrHeap.
*/
typedef struct NtrHeapSlot NtrHeapSlot;

/**
   @brief Type of heap-based priority queue.
*/
typedef struct NtrHeap NtrHeap;

/**
   @brief Data structure for partitioned transition relation.
*/
typedef struct NtrPartTR {
  int nparts;			/**< number of parts */
  DdNode **part;		/**< array of parts */
  DdNode **icube;		/**< quantification cubes for image */
  DdNode **pcube;		/**< quantification cubes for preimage */
  DdNode **nscube;		/**< next state variables in each part */
  DdNode *preiabs;		/**< present state vars and inputs in no part */
  DdNode *prepabs;		/**< inputs in no part */
  DdNode *xw;			/**< cube of all present states and PIs */
  NtrHeap *factors;		/**< factors extracted from the image */
  int nlatches;		/**< number of latches */
  DdNode **x;			/**< array of present state variables */
  DdNode **y;			/**< array of next state variables */
} NtrPartTR;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

#ifndef TRUE
#   define TRUE 1
#endif
#ifndef FALSE
#   define FALSE 0
#endif

/**
  @brief Returns 1 if the two arguments are identical strings.

  @sideeffect none

*/
#define STRING_EQUAL(s1,s2) (strcmp((s1),(s2)) == 0)


/** \cond */
extern int Ntr_buildBKFDDs (BnetNetwork *net, DdManager *dd, NtrOptions *option, BnetNetwork *net2);

/** \endcond */


#ifdef __cplusplus
}
#endif

#endif /* _NTR */
