/**
  @file

  @ingroup testbkfdd

  @brief Main program for the nanotrav program.

   @author Xuanxiang Huang

  @copyright
  Copyright (c) 2019-, Jinan University, Guangzhou, China.

  All rights reserved.

======================================================================
	@Modification and Extension details
		1. Delete some unneeded code blocks.
		2. Initialize newly added arguments in mainInit.
		3. Add arguments to ntrReadOptions.
		4. Add CheckBkfddNodes to check BKFDD nodes.
		surrounded by	"Xuanxiang Huang" or "BKFDD"
		5. Allow adding automethd to DDmanager even though autodyn is disable.
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

#define NTR_VERSION "Nanotrav Version #0.13, Release date 2020/09/18"

#define BUFLENGTH 8192

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/
//#define DD_DEBUG 100
static  char    buffer[BUFLENGTH];

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/** \cond */

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static NtrOptions * mainInit ();
static void ntrReadOptions (int argc, char **argv, NtrOptions *option);
static void ntrReadOptionsFile (char *name, char ***argv, int *argc);
static char* readLine (FILE *fp);
static FILE * open_file (char *filename, const char *mode);
static int reorder (BnetNetwork *net, DdManager *dd, NtrOptions *option);
static void freeOption (NtrOptions *option);
static DdManager * startCudd (NtrOptions *option, int nvars);
//static int CheckBkfddNodes(DdManager * dd);

/** \endcond */


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**
  @brief Main program for ntr.

  @details Performs initialization. Reads command line options and
  network(s). Builds BKFDDs with reordering, and optionally does
  reachability analysis. Prints stats.

  @sideeffect None

*/
int
main(
  int  argc,
  char ** argv)
{
  NtrOptions	*option;	/* options */
  FILE	*fp1;		/* first network file pointer */
  BnetNetwork	*net1 = NULL;	/* first network */
  DdManager	*dd;		/* pointer to DD manager */
  int		exitval;	/* return value of Cudd_CheckZeroRef */
  int		ok;		/* overall return value from main() */
  int		result;		/* stores the return value of functions */
  BnetNode	*node;		/* auxiliary pointer to network node */
  int		pr;		/* verbosity level */

  /* Initialize. */
#if defined(_WIN32) && defined(_TWO_DIGIT_EXPONENT)
  (void) _set_output_format(_TWO_DIGIT_EXPONENT);
#endif
  option = mainInit();
  ntrReadOptions(argc,argv,option);
  pr = option->verb;

	/* Read the first network... */
	fp1 = open_file(option->file1, "r");
	net1 = Bnet_ReadNetwork(fp1,pr);
	(void) fclose(fp1);
	if (net1 == NULL) {
		(void) fprintf(stderr,"Syntax error in %s.\n",option->file1);
		exit(2);
	}
	/* ... and optionally echo it to the standard output. */
	if (pr > 2) {
		Bnet_PrintNetwork(net1);
	}

  /* Initialize manager. We start with 0 variables, because
  ** Ntr_buildDDs will create new variables rather than using
  ** whatever already exists.
  */
  dd = startCudd(option,net1->ninputs);
  if (dd == NULL) { exit(2); }

  /* Build the BKFDDs for the nodes of the first network. */

	/* use BKFDD to build first DD, and use CUDD to build second DD,
		then check whether these two are equivalent. */
	result = Ntr_buildBKFDDs(net1,dd,option,NULL);
  if (result == 0) { exit(2); }

	if (option->locGlob != BNET_LOCAL_DD) {
	/* Print the order before the final reordering. */
	(void) printf("Order before final reordering\n");
	result = Bnet_PrintOrder(net1,dd);
	if (result == 0) exit(2);
	}

	/* Perform final reordering if requested. */
	result = reorder(net1,dd,option);
	if (result == 0) exit(2);

	/* No more auto GC or reordering allowed. */
	Cudd_DisableGarbageCollection(dd);
	Cudd_AutodynDisable(dd);

	// Introduce pD expansions to BKFDDs
	int fix_cano = 1;//0;
	unsigned long transStart = util_cpu_time();
	long transSize1 = Cudd_ReadNodeCount(dd);
	if (option->reordering == BKFDD_GROUP_MIX ||
			option->reordering == BKFDD_SYMM_MIX ||
			option->reordering == BKFDD_OET_SIFT ||
			option->reordering == BKFDD_GROUP_NMEG_MIX) {
		chooseSD6(dd);
		/* once introduce pD expansions, we
			need to fix canonicity of DD nodes*/
				if (fix_Canonicity(dd, net1, dd->size-1) == 0) {
			printf("fix canonicity failed\n");
		} else {
			fix_cano = 1;
		}
	} else if (option->reordering == KFDD_GROUP_MIX ||
						option->reordering == KFDD_SYMM_MIX) {
		chooseSD3(dd);
		if (fix_Canonicity(dd, net1, dd->size-1) == 0) {
			printf("fix canonicity failed\n");
		} else {
			fix_cano = 1;
		}
	}
	unsigned long transEnd = util_cpu_time();
	long transSize2 = Cudd_ReadNodeCount(dd);

	printf("\tBKFDD Transformation runtime: %4g\n", (double)(transEnd - transStart)/1000.0);
	printf("\tBKFDD Transformation size, from %ld to %ld\n", transSize1, transSize2);

	if (dd->interact != NULL) {
		FREE(dd->interact);
	}
#if 0	
	/* check before RC detection. */
	int checkVal = Cudd_DebugCheck(dd);
	if (checkVal != 0) {
		(void) fflush(stdout);
		(void) fprintf(stderr, "Cudd_DebugCheck failed\n");
		exit(2);
	}
	checkVal = Cudd_CheckKeys(dd);
	if (checkVal != 0) {
		(void) fflush(stdout);
		(void) fprintf(stderr, "Cudd_CheckKeys failed\n");
		exit(2);
	}

	/* Check BKFDD nodes. Make sure BKFDD node count 
		is equal to "Final Size" reported by CUDD. */
	int checkRet = CheckBkfddNodes(dd);
	if (checkRet == 0) {
		(void) fflush(stdout);
		(void) fprintf(stderr, "CheckBkfddNodes failed\n");
		exit(2);
	}

	int RCdetect, RCreduce;
	RCdetect = RCreduce = 0;
	unsigned long checkRCTime = util_cpu_time();
	
	if (!Bkfdd_RC_Detection(dd, &RCdetect, &RCreduce)) {
		fprintf(stderr, "RC detection failed\n");
		exit(2);
	}
	
	printf("\t[RC]: %d nodes detected, reduce %d nodes has effect on DD size. Check in %4g sec\n",
	RCdetect, RCreduce, (double)(util_cpu_time() - checkRCTime)/1000.0);
	printf("\tBKFDD final size can be %ld\n", transSize2-RCreduce);
	
	/* Final Check. */
	checkVal = Cudd_DebugCheck(dd);
	if (checkVal != 0) {
		(void) fflush(stdout);
		(void) fprintf(stderr, "Cudd_DebugCheck failed\n");
		exit(2);
	}
	checkVal = Cudd_CheckKeys(dd);
	if (checkVal != 0) {
		(void) fflush(stdout);
		(void) fprintf(stderr, "Cudd_CheckKeys failed\n");
		exit(2);
	}
#endif
	/* Print final order. */
	if ((option->reordering != CUDD_REORDER_NONE || option->gaOnOff) &&
	option->locGlob != BNET_LOCAL_DD) {
		(void) printf("New order\n");
		result = Bnet_PrintOrder(net1,dd);
		if (result == 0) exit(2);
	}
	
	/* Dump BKFDDs if so requested. */
	if ( (fix_cano == 1) && option->bdddump && option->second == FALSE &&
	option->density == FALSE && option->decomp == FALSE &&
	option->cofest == FALSE && option->clip < 0.0 &&
	option->scc == FALSE) {
		(void) printf("Dumping BKFDDs to %s\n", option->dumpfile);
		if (option->node != NULL) {
			printf("unimplemented in BKFDDs\n");
			if (!st_lookup(net1->hash,option->node,(void **)&node)) {
				exit(2);
			}
			result = Bnet_bkfddArrayDump(dd,net1,option->dumpfile,&(node->dd),
			&(node->name),1);
		} else { // option->node == NULL
			result = Bnet_bkfddDump(dd, net1, option->dumpfile);
		}
		if (result != 1) {
			(void) printf("BKFDD dump failed.\n");
		}
	}

    /* Print stats and clean up. */
	if (pr >= 0) {
		result = Cudd_PrintInfo(dd,stdout);
		if (result != 1) {
			(void) printf("Cudd_PrintInfo failed.\n");
		}
	}

#if defined(DD_DEBUG) && !defined(DD_NO_DEATH_ROW)
  (void) fprintf(dd->err,"%d empty slots in death row\n",
  cuddTimesInDeathRow(dd,NULL));
#endif
  (void) printf("Final size: %ld\n", Cudd_ReadNodeCount(dd));

	/* Dispose of node BKFDDs. */
	node = net1->nodes;
	while (node != NULL) {
		if (node->dd != NULL &&
		node->type != BNET_INPUT_NODE &&
		node->type != BNET_PRESENT_STATE_NODE) {
			Cudd_IterDerefBdd(dd,node->dd);
			node->dd = NULL;
		}
		node = node->next;
	}
	/* Dispose of network. */
	Bnet_FreeNetwork(net1);

	/* Check reference counts: At this point we should have dereferenced
	** everything we had, except in the case of re-encoding.
	*/
	exitval = Cudd_CheckZeroRef(dd);
	ok = exitval != 0;  /* ok == 0 means O.K. */
	if (exitval != 0) {
		(void) fflush(stdout);
		(void) fprintf(stderr,
		"%d non-zero DD reference counts after dereferencing\n", exitval);
	}

#ifdef DD_DEBUG
  Cudd_CheckKeys(dd);
#endif

  Cudd_Quit(dd);

  if (pr >= 0) (void) printf("total time = %s\n",
    util_print_time(util_cpu_time() - option->initialTime));
  freeOption(option);
  if (pr >= 0) util_print_cpu_stats(stdout);

  exit(ok);

} /* end of main */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**
  @brief Allocates the option structure and initializes it.

  @sideeffect none

  @see ntrReadOptions

*/
static NtrOptions *
mainInit(
   )
{
	NtrOptions	*option;

	/* Initialize option structure. */
	option = ALLOC(NtrOptions,1);
	option->initialTime    = util_cpu_time();
	option->verify         = FALSE;
	option->second         = FALSE;
	option->file1          = NULL;
	option->file2          = NULL;
	option->traverse       = FALSE;
	option->depend         = FALSE;
	option->image          = NTR_IMAGE_MONO;
	option->imageClip      = 1.0;
	option->approx         = NTR_UNDER_APPROX;
	option->threshold      = -1;
	option->from	   = NTR_FROM_NEW;
	option->groupnsps      = NTR_GROUP_NONE;
	option->closure        = FALSE;
	option->closureClip    = 1.0;
	option->envelope       = FALSE;
	option->scc            = FALSE;
	option->maxflow        = FALSE;
	option->shortPath      = NTR_SHORT_NONE;
	option->selectiveTrace = FALSE;
	option->zddtest        = FALSE;
	option->printcover     = FALSE;
	option->sinkfile       = NULL;
	option->partition      = FALSE;
	option->char2vect      = FALSE;
	option->density        = FALSE;
	option->quality        = 1.0;
	option->decomp         = FALSE;
	option->cofest         = FALSE;
	option->clip           = -1.0;
	option->dontcares      = FALSE;
	option->closestCube    = FALSE;
	option->clauses        = FALSE;
	option->noBuild        = FALSE;
	option->stateOnly      = FALSE;
	option->node           = NULL;
	option->locGlob        = BNET_GLOBAL_DD;
	option->progress       = FALSE;
	option->cacheSize      = 32768;
	option->maxMemory      = 0;	/* set automatically */
	option->maxMemHard     = 0; /* don't set */
	option->maxLive        = ~0U; /* very large number */
	option->slots          = CUDD_UNIQUE_SLOTS;
	option->ordering       = PI_PS_FROM_FILE;
	option->orderPiPs      = NULL;
	option->reordering     = CUDD_REORDER_NONE;
	option->autoMethod     = CUDD_REORDER_SIFT;
	option->autoDyn        = 0;
	option->treefile       = NULL;
	option->firstReorder   = DD_FIRST_REORDER;
	option->countDead      = FALSE;
	option->maxGrowth      = 20;
	option->groupcheck     = CUDD_GROUP_CHECK7;
	option->arcviolation   = 10;
	option->symmviolation  = 10;
	option->recomb         = DD_DEFAULT_RECOMB;
	option->nodrop         = TRUE;
	option->signatures     = FALSE;
	option->verb           = 0;
	option->gaOnOff        = 0;
	option->populationSize = 0;	/* use default */
	option->numberXovers   = 0;	/* use default */
	option->bdddump	   = FALSE;
	option->dumpFmt	   = 0;	/* dot */
	option->dumpfile	   = NULL;
	option->store          = -1; /* do not store */
	option->storefile      = NULL;
	option->load           = FALSE;
	option->loadfile       = NULL;
	option->seed           = 1;

/** Xuanxiang Huang:BKFDD */
	option->davioExist = 30;
	option->chooseLowBound = 70;
	option->chooseNew = 10000;
	option->chooseDav = 10000;
	option->chooseFail = 200;
	option->bkfddMode = MODE_SND;
/** Xuanxiang Huang:BKFDD */

	return(option);

} /* end of mainInit */


/**
  @brief Reads the command line options.

  @details Scans the command line one argument at a time and performs
  a switch on each arguement it hits.  Some arguemnts also read in the
  following arg from the list (i.e., -f also gets the filename which
  should folow.)  Gives a usage message and exits if any unrecognized
  args are found.

  @sideeffect May initialize the random number generator.

  @see mainInit ntrReadOptionsFile

*/
static void
ntrReadOptions(
  int  argc,
  char ** argv,
  NtrOptions * option)
{
	int	i = 0;

	if (argc < 2) goto usage;

	if (STRING_EQUAL(argv[1],"-f")) {
	ntrReadOptionsFile(argv[2],&argv,&argc);
	}

	for (i = 1; i < argc; i++) {
	if (argv[i][0] != '-' ) {
		if (option->file1 == NULL) {
		option->file1 = util_strsav(argv[i]);
		} else {
		goto usage;
		}
	} else if (STRING_EQUAL(argv[i],"-threshold")) {
	i++;
	option->threshold = (int) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-groupnsps")) {
	i++;
	if (STRING_EQUAL(argv[i],"none")) {
	option->groupnsps = NTR_GROUP_NONE;
	} else if (STRING_EQUAL(argv[i],"default")) {
	option->groupnsps = NTR_GROUP_DEFAULT;
	} else if (STRING_EQUAL(argv[i],"fixed")) {
	option->groupnsps = NTR_GROUP_FIXED;
	} else {
	goto usage;
	}
	} else if (STRING_EQUAL(argv[i],"-progress")) {
	option->progress = TRUE;
	} else if (STRING_EQUAL(argv[i],"-cache")) {
	i++;
	option->cacheSize = (int) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-maxmem")) {
	i++;
	option->maxMemory = 1048576 * (int) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-memhard")) {
	i++;
	option->maxMemHard = 1048576 * (int) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-maxlive")) {
	i++;
	option->maxLive = (unsigned int) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-slots")) {
	i++;
	option->slots = (int) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-ordering")) {
		i++;
		if (STRING_EQUAL(argv[i],"dfs")) {
		option->ordering = PI_PS_DFS;
		} else if (STRING_EQUAL(argv[i],"hw")) {
		option->ordering = PI_PS_FROM_FILE;
		} else {
		goto usage;
		}
	} else if (STRING_EQUAL(argv[i],"-order")) {
	i++;
	option->ordering = PI_PS_GIVEN;
	option->orderPiPs = util_strsav(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-reordering")) {
		i++;
		if (STRING_EQUAL(argv[i],"none")) {
		option->reordering = CUDD_REORDER_NONE;
		} else if (STRING_EQUAL(argv[i],"random")) {
		option->reordering = CUDD_REORDER_RANDOM;
		} else if (STRING_EQUAL(argv[i],"bernard") ||
		STRING_EQUAL(argv[i],"pivot")) {
		option->reordering = CUDD_REORDER_RANDOM_PIVOT;
		} else if (STRING_EQUAL(argv[i],"sifting")) {
		option->reordering = CUDD_REORDER_SIFT;
		} else if (STRING_EQUAL(argv[i],"converge")) {
		option->reordering = CUDD_REORDER_SIFT_CONVERGE;
		} else if (STRING_EQUAL(argv[i],"symm")) {
		option->reordering = CUDD_REORDER_SYMM_SIFT;
		} else if (STRING_EQUAL(argv[i],"cosymm")) {
		option->reordering = CUDD_REORDER_SYMM_SIFT_CONV;
		} else if (STRING_EQUAL(argv[i],"tree") ||
		STRING_EQUAL(argv[i],"group")) {
		option->reordering = CUDD_REORDER_GROUP_SIFT;
		} else if (STRING_EQUAL(argv[i],"cotree") ||
		STRING_EQUAL(argv[i],"cogroup")) {
		option->reordering = CUDD_REORDER_GROUP_SIFT_CONV;
		} else if (STRING_EQUAL(argv[i],"win2")) {
		option->reordering = CUDD_REORDER_WINDOW2;
		} else if (STRING_EQUAL(argv[i],"win3")) {
		option->reordering = CUDD_REORDER_WINDOW3;
		} else if (STRING_EQUAL(argv[i],"win4")) {
		option->reordering = CUDD_REORDER_WINDOW4;
		} else if (STRING_EQUAL(argv[i],"win2conv")) {
		option->reordering = CUDD_REORDER_WINDOW2_CONV;
		} else if (STRING_EQUAL(argv[i],"win3conv")) {
		option->reordering = CUDD_REORDER_WINDOW3_CONV;
		} else if (STRING_EQUAL(argv[i],"win4conv")) {
		option->reordering = CUDD_REORDER_WINDOW4_CONV;
		} else if (STRING_EQUAL(argv[i],"annealing")) {
		option->reordering = CUDD_REORDER_ANNEALING;
		} else if (STRING_EQUAL(argv[i],"genetic")) {
		option->reordering = CUDD_REORDER_GENETIC;
		} else if (STRING_EQUAL(argv[i],"linear")) {
		option->reordering = CUDD_REORDER_LINEAR;
		} else if (STRING_EQUAL(argv[i],"linconv")) {
		option->reordering = CUDD_REORDER_LINEAR_CONVERGE;
		} else if (STRING_EQUAL(argv[i],"exact")) {
		option->reordering = CUDD_REORDER_EXACT;
/** Xuanxiang Huang:BKFDD */
		} else if (STRING_EQUAL(argv[i],"kfddsymm")) {
		option->reordering = KFDD_SYMM_SIFT;
		} else if (STRING_EQUAL(argv[i],"bkfddsymm")){
		option->reordering = BKFDD_SYMM_SIFT;
		} else if (STRING_EQUAL(argv[i],"kfddgroup")) {
		option->reordering = KFDD_GROUP_SIFT;
		} else if (STRING_EQUAL(argv[i],"bkfddgroup")){
		option->reordering = BKFDD_GROUP_SIFT;
		} else if (STRING_EQUAL(argv[i],"bkfddgroupnmeg")){
		option->reordering = BKFDD_GROUP_SIFT_NMEG;
		} else if (STRING_EQUAL(argv[i],"biddgroup")){
		option->reordering = BIDD_GROUP_SIFT;
		} else if (STRING_EQUAL(argv[i],"oet")) {
		option->reordering = BKFDD_OET_SIFT;
		} else if (STRING_EQUAL(argv[i],"bkfdd-symm-mix")) {
		option->reordering = BKFDD_SYMM_MIX;
		} else if (STRING_EQUAL(argv[i],"kfdd-symm-mix")) {
		option->reordering = KFDD_SYMM_MIX;
		} else if (STRING_EQUAL(argv[i],"bkfdd-group-mix")) {
		option->reordering = BKFDD_GROUP_MIX;
		} else if (STRING_EQUAL(argv[i],"kfdd-group-mix")) {
		option->reordering = KFDD_GROUP_MIX;
		} else if (STRING_EQUAL(argv[i],"bkfdd-group-nmeg-mix")) {
		option->reordering = BKFDD_GROUP_NMEG_MIX;
/** Xuanxiang Huang:BKFDD */
		} else {
		goto usage;
		}
	} else if (STRING_EQUAL(argv[i],"-autodyn")) {
	option->autoDyn = 3;
	} else if (STRING_EQUAL(argv[i],"-autodynB")) {
	option->autoDyn |= 1;
	} else if (STRING_EQUAL(argv[i],"-autodynZ")) {
	option->autoDyn |= 2;
	} else if (STRING_EQUAL(argv[i],"-automethod")) {
		i++;
		if (STRING_EQUAL(argv[i],"none")) {
		option->autoMethod = CUDD_REORDER_NONE;
		} else if (STRING_EQUAL(argv[i],"random")) {
		option->autoMethod = CUDD_REORDER_RANDOM;
		} else if (STRING_EQUAL(argv[i],"bernard") ||
		STRING_EQUAL(argv[i],"pivot")) {
		option->autoMethod = CUDD_REORDER_RANDOM_PIVOT;
		} else if (STRING_EQUAL(argv[i],"sifting")) {
		option->autoMethod = CUDD_REORDER_SIFT;
		} else if (STRING_EQUAL(argv[i],"converge")) {
		option->autoMethod = CUDD_REORDER_SIFT_CONVERGE;
		} else if (STRING_EQUAL(argv[i],"symm")) {
		option->autoMethod = CUDD_REORDER_SYMM_SIFT;
		} else if (STRING_EQUAL(argv[i],"cosymm")) {
		option->autoMethod = CUDD_REORDER_SYMM_SIFT_CONV;
		} else if (STRING_EQUAL(argv[i],"tree") ||
		STRING_EQUAL(argv[i],"group")) {
		option->autoMethod = CUDD_REORDER_GROUP_SIFT;
		} else if (STRING_EQUAL(argv[i],"cotree") ||
		STRING_EQUAL(argv[i],"cogroup")) {
		option->autoMethod = CUDD_REORDER_GROUP_SIFT_CONV;
		} else if (STRING_EQUAL(argv[i],"win2")) {
		option->autoMethod = CUDD_REORDER_WINDOW2;
		} else if (STRING_EQUAL(argv[i],"win3")) {
		option->autoMethod = CUDD_REORDER_WINDOW3;
		} else if (STRING_EQUAL(argv[i],"win4")) {
		option->autoMethod = CUDD_REORDER_WINDOW4;
		} else if (STRING_EQUAL(argv[i],"win2conv")) {
		option->autoMethod = CUDD_REORDER_WINDOW2_CONV;
		} else if (STRING_EQUAL(argv[i],"win3conv")) {
		option->autoMethod = CUDD_REORDER_WINDOW3_CONV;
		} else if (STRING_EQUAL(argv[i],"win4conv")) {
		option->autoMethod = CUDD_REORDER_WINDOW4_CONV;
		} else if (STRING_EQUAL(argv[i],"annealing")) {
		option->autoMethod = CUDD_REORDER_ANNEALING;
		} else if (STRING_EQUAL(argv[i],"genetic")) {
		option->autoMethod = CUDD_REORDER_GENETIC;
		} else if (STRING_EQUAL(argv[i],"linear")) {
		option->autoMethod = CUDD_REORDER_LINEAR;
		} else if (STRING_EQUAL(argv[i],"linconv")) {
		option->autoMethod = CUDD_REORDER_LINEAR_CONVERGE;
		} else if (STRING_EQUAL(argv[i],"exact")) {
		option->autoMethod = CUDD_REORDER_EXACT;
	/** Xuanxiang Huang:BKFDD */
		} else if (STRING_EQUAL(argv[i],"kfddsymm")) {
		option->autoMethod = KFDD_SYMM_SIFT;
		} else if (STRING_EQUAL(argv[i],"bkfddsymm")) {
		option->autoMethod = BKFDD_SYMM_SIFT;
		} else if (STRING_EQUAL(argv[i],"kfddgroup")) {
		option->autoMethod = KFDD_GROUP_SIFT;
		} else if (STRING_EQUAL(argv[i],"bkfddgroup")) {
		option->autoMethod = BKFDD_GROUP_SIFT;
		} else if (STRING_EQUAL(argv[i],"bkfddgroupnmeg")) {
		option->autoMethod = BKFDD_GROUP_SIFT_NMEG;
		} else if (STRING_EQUAL(argv[i],"bidd")) {
		option->autoMethod = BIDD_GROUP_SIFT;
		} else if (STRING_EQUAL(argv[i],"oet")) {
		option->autoMethod = BKFDD_OET_SIFT;
		}else {
		goto usage;
		}
	} else if (STRING_EQUAL(argv[i],"-davioexist")) {
	i ++;
	option->davioExist = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-chooselowbound")) {
	i ++;
	option->chooseLowBound = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-choosenew")) {
	i ++;
	option->chooseNew = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-choosedav")) {
	i ++;
	option->chooseDav = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-choosefail")) {
	i ++;
	option->chooseFail = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-sndmode")) {
	option->bkfddMode = MODE_SND;
	} else if (STRING_EQUAL(argv[i],"-sdmode")) {
	option->bkfddMode = MODE_SD;
/** Xuanxiang Huang:BKFDD */
	} else if (STRING_EQUAL(argv[i],"-first")) {
	i++;
	option->firstReorder = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-countdead")) {
	option->countDead = TRUE;
	} else if (STRING_EQUAL(argv[i],"-growth")) {
	i++;
	option->maxGrowth = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-groupcheck")) {
		i++;
		if (STRING_EQUAL(argv[i],"check")) {
		option->groupcheck = CUDD_GROUP_CHECK;
		} else if (STRING_EQUAL(argv[i],"nocheck")) {
		option->groupcheck = CUDD_NO_CHECK;
		} else if (STRING_EQUAL(argv[i],"check2")) {
		option->groupcheck = CUDD_GROUP_CHECK2;
		} else if (STRING_EQUAL(argv[i],"check3")) {
		option->groupcheck = CUDD_GROUP_CHECK3;
		} else if (STRING_EQUAL(argv[i],"check4")) {
		option->groupcheck = CUDD_GROUP_CHECK4;
		} else if (STRING_EQUAL(argv[i],"check5")) {
		option->groupcheck = CUDD_GROUP_CHECK5;
		} else if (STRING_EQUAL(argv[i],"check6")) {
		option->groupcheck = CUDD_GROUP_CHECK6;
		} else if (STRING_EQUAL(argv[i],"check7")) {
		option->groupcheck = CUDD_GROUP_CHECK7;
		} else if (STRING_EQUAL(argv[i],"check8")) {
		option->groupcheck = CUDD_GROUP_CHECK8;
		} else if (STRING_EQUAL(argv[i],"check9")) {
		option->groupcheck = CUDD_GROUP_CHECK9;
		} else if (STRING_EQUAL(argv[i],"bkfcheck1")) {
		option->groupcheck = BKFDD_GROUP_CHECK1;
		} else if (STRING_EQUAL(argv[i],"bkfcheck2")) {
		option->groupcheck = BKFDD_GROUP_CHECK2;
		}	else {
		goto usage;
		}
	} else if (STRING_EQUAL(argv[i],"-arcviolation")) {
	    i++;
	    option->arcviolation = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-symmviolation")) {
	    i++;
	    option->symmviolation = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-drop")) {
	option->nodrop = FALSE;
	} else if (STRING_EQUAL(argv[i],"-sign")) {
	option->signatures = TRUE;
	} else if (STRING_EQUAL(argv[i],"-genetic")) {
	option->gaOnOff = 1;
	} else if (STRING_EQUAL(argv[i],"-genepop")) {
	option->gaOnOff = 1;
	i++;
	option->populationSize = (int)atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-genexover")) {
	option->gaOnOff = 1;
	i++;
	option->numberXovers = (int) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-seed")) {
	i++;
	option->seed = (int32_t) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-dumpfile")) {
	i++;
	option->bdddump = TRUE;
	option->dumpfile = util_strsav(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-dumpblif")) {
	option->dumpFmt = 1; /* blif */
	} else if (STRING_EQUAL(argv[i],"-store")) {
	i++;
	option->store = (int) atoi(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-storefile")) {
	i++;
	option->storefile = util_strsav(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-loadfile")) {
	i++;
	option->load = 1;
	option->loadfile = util_strsav(argv[i]);
	} else if (STRING_EQUAL(argv[i],"-p")) {
	i++;
	option->verb = (int) atoi(argv[i]);
	} else {
	goto usage;
	}
	}

	if (option->store >= 0 && option->storefile == NULL) {
	(void) fprintf(stdout,"-storefile mandatory with -store\n");
	exit(-1);
	}

	if (option->verb >= 0) {
	(void) printf("# %s\n", NTR_VERSION);
	/* echo command line and arguments */
	(void) printf("#");
	for (i = 0; i < argc; i++) {
	(void) printf(" %s", argv[i]);
	}
	(void) printf("\n");
	(void) printf("# CUDD Version ");
	Cudd_PrintVersion(stdout);
	(void) fflush(stdout);
	}

	return;

usage:	/* convenient goto */
	printf("Usage: please read man page\n");
	if (i == 0) {
	(void) fprintf(stdout,"too few arguments\n");
	} else {
	(void) fprintf(stdout,"option: %s is not defined\n",argv[i]);
	}
	exit(-1);

} /* end of ntrReadOptions */


/**
  @brief Reads the program options from a file.

  @details Opens file. Reads the command line from the otpions file
  using the read_line func. Scans the line looking for spaces, each
  space is a searator and demarks a new option.  When a space is
  found, it is changed to a \0 to terminate that string; then the next
  value of slot points to the next non-space character.  There is a
  limit of 1024 options.  Should produce an error (presently doesn't)
  on overrun of options, but this is very unlikely to happen.

  @sideeffect none

*/
static void
ntrReadOptionsFile(
  char * name,
  char *** argv,
  int * argc)
{
	char	**slot;
	char	*line;
	char	c;
	int		index,flag;
	FILE	*fp;

	if ((fp = fopen(name,"r")) == NULL) {
	fprintf(stderr,"Error: can not find cmd file %s\n",name);
	exit(-1);
	}

	slot = ALLOC(char *,1024);
	index = 1;
	line = readLine(fp);
	flag = TRUE;

	do {
	c = *line;
	if ( c == ' ')  {
	flag = TRUE;
	*line = '\0';
	} else if ( c != ' ' && flag == TRUE) {
	flag = FALSE;
	slot[index] = line;
	index++;
	}
	line++;
	} while ( *line != '\0');


	*argv = slot;
	*argc = index;

	fclose(fp);

} /* end of ntrReadOptionsFile */


/**
  @brief Reads a line from the option file.

  @sideeffect none

*/
static char*
readLine(
  FILE * fp)
{
	int  c;
	char *pbuffer;

	pbuffer = buffer;

	/* Strip white space from beginning of line. */
	for(;;) {
	c = getc(fp);
	if ( c == EOF) return(NULL);
	if ( c == '\n') {
	*pbuffer = '\0';
	return(buffer); /* got a blank line */
	}
	if ( c != ' ') break;
	}
	do {
	if ( c == '\\' ) { /* if we have a continuation character.. */
	do {	/* scan to end of line */
	c = getc(fp);
	if ( c == '\n' ) break;
	} while ( c != EOF);
	if ( c != EOF) {
	*pbuffer = ' ';
	pbuffer++;
	} else return( buffer);
	c = getc(fp);
	continue;
	}
	*pbuffer = (char) c;
	pbuffer++;
	c = getc(fp);
	} while( c != '\n' &&  c != EOF);
	*pbuffer = '\0';
	return(buffer);

} /* end of readLine */


/**
  @brief Opens a file.

  @details Opens a file, or fails with an error message and exits.
  Allows '-' as a synonym for standard input.

  @sideeffect None

*/
static FILE *
open_file(
  char * filename,
  const char * mode)
{
	FILE *fp;

	if (strcmp(filename, "-") == 0) {
	return mode[0] == 'r' ? stdin : stdout;
	} else if ((fp = fopen(filename, mode)) == NULL) {
	perror(filename);
	exit(1);
	}
	return(fp);

} /* end of open_file */


/**
  @brief Explicitly applies reordering to the DDs.

  @return 1 if successful; 0 otherwise.

  @sideeffect None

*/
static int
reorder(
  BnetNetwork * net,
  DdManager * dd,
  NtrOptions * option)
{
	int result;			/* return value from functions */

	(void) printf("Number of inputs = %d\n",net->ninputs);

	/* Perform the final reordering */
	if (option->reordering != CUDD_REORDER_NONE) {
#ifdef DD_DEBUG
		result = Cudd_DebugCheck(dd);
		if (result != 0) {
			(void) fprintf(stderr,"Error reported by Cudd_DebugCheck\n");
			return(0);
		}
		result = Cudd_CheckKeys(dd);
		if (result != 0) {
			(void) fprintf(stderr,"Error reported by Cudd_CheckKeys\n");
			return(0);
		}
#endif

		dd->siftMaxVar = 1000000;
		dd->siftMaxSwap = 1000000000;
		if (option->reordering == BKFDD_OET_SIFT) {
			result = bkfdd_reorder_bnet(dd,option->reordering,1,net);
			if (result == 0) return(0);
		} else {
			result = Cudd_ReduceHeap(dd,option->reordering,1);
			if (result == 0) return(0);
		}

#ifdef DD_DEBUG
		result = Cudd_DebugCheck(dd);
		if (result != 0) {
			(void) fprintf(stderr,"Error reported by Cudd_DebugCheck\n");
			return(0);
		}
		result = Cudd_CheckKeys(dd);
		if (result != 0) {
			(void) fprintf(stderr,"Error reported by Cudd_CheckKeys\n");
			return(0);
		}
#endif

		/* Print symmetry stats if pertinent */
		if (dd->tree == NULL &&
		(option->reordering == CUDD_REORDER_SYMM_SIFT ||
		option->reordering == CUDD_REORDER_SYMM_SIFT_CONV))
			Cudd_SymmProfile(dd,0,dd->size - 1);
	}

	if (option->gaOnOff) {
		result = Cudd_ReduceHeap(dd,CUDD_REORDER_GENETIC,1);
		if (result == 0) {
			(void) printf("Something went wrong in cuddGa\n");
			return(0);
		}
	}

	return(1);

} /* end of reorder */


/**
  @brief Frees the option structure and its appendages.

  @sideeffect None

*/
static void
freeOption(
  NtrOptions * option)
{
  if (option->file1 != NULL) FREE(option->file1);
  if (option->file2 != NULL) FREE(option->file2);
  if (option->orderPiPs != NULL) FREE(option->orderPiPs);
  if (option->treefile != NULL) FREE(option->treefile);
  if (option->sinkfile != NULL) FREE(option->sinkfile);
  if (option->dumpfile != NULL) FREE(option->dumpfile);
  if (option->loadfile != NULL) FREE(option->loadfile);
  if (option->storefile != NULL) FREE(option->storefile);
  if (option->node != NULL) FREE(option->node);
  FREE(option);

} /* end of freeOption */


/**
  @brief Starts the CUDD manager with the desired options.

  @details Starts with 0 variables, because Ntr_buildDDs will create
  new variables rather than using whatever already exists.

  @sideeffect None

*/
static DdManager *
startCudd(
  NtrOptions * option,
  int  nvars)
{
	DdManager *dd;
	int result;

	dd = Cudd_Init(0, 0, option->slots, option->cacheSize, option->maxMemory);
	if (dd == NULL) return(NULL);

	Cudd_Srandom(dd, option->seed);
	if (option->maxMemHard != 0) {
	Cudd_SetMaxMemory(dd,option->maxMemHard);
	}
	Cudd_SetMaxLive(dd,option->maxLive);
	Cudd_SetGroupcheck(dd,option->groupcheck);
	if (option->autoDyn & 1) {
	Cudd_AutodynEnable(dd,option->autoMethod);
	}
/** Xuanxiang Huang:BKFDD, add automethod to DDmanager even though autodyn is disable,
	cause we want to reordering by hand. */	
	if (option->autoMethod != CUDD_REORDER_SAME) {
		dd->autoMethod = option->autoMethod;
	}
/** Xuanxiang Huang:BKFDD */
	
	dd->nextDyn = option->firstReorder;
	dd->countDead = (option->countDead == FALSE) ? ~0 : 0;
	dd->maxGrowth = 1.0 + ((float) option->maxGrowth / 100.0);
	dd->recomb = option->recomb;
	dd->arcviolation = option->arcviolation;
	dd->symmviolation = option->symmviolation;
	dd->populationSize = option->populationSize;
	dd->numberXovers = option->numberXovers;
	dd->davio_exist_factor = ((double) option->davioExist / 100.0); /** 0 <= davioExistFactor */
	dd->choose_lower_bound_factor = ((double) option->chooseLowBound / 100.0); /** 0 <= chooseLowBoundFactor < 1 */
	dd->choose_new_bound_factor = ((double) option->chooseNew / 10000.0);
	dd->choose_dav_bound_factor = ((double) option->chooseDav / 10000.0);
	dd->choose_fail_bound_factor = ((double) option->chooseFail / 100.0);
	dd->bkfddMode = option->bkfddMode;
	dd->choose_threshold = 4004; /* init choose threshold for chooseSD3, chooseSD6. */
	if (dd->davio_exist_factor < 0) {
		dd->davio_exist_factor = 0;
	}
	if (dd->choose_lower_bound_factor >= 1) {
		dd->choose_lower_bound_factor = 1;
	} else if (dd->choose_lower_bound_factor < 0) {
		dd->choose_lower_bound_factor = 0;
	}
	if (dd->choose_new_bound_factor < 0) {
		dd->choose_new_bound_factor = 1;
	}
	if (dd->choose_dav_bound_factor < 0) {
		dd->choose_dav_bound_factor = 1;
	}
	if (dd->choose_fail_bound_factor < 0) {
		dd->choose_fail_bound_factor = 1;
	}
	printf("\tMode: ");
	if (option->bkfddMode == MODE_SD) {
		printf("All expns mix during building\n");
	} else {
		printf("Only S and ND during building\n");
	}
	printf("\tstartCudd: davio_exist_factor = %lf, choose_lower_bound_factor = %lf, choose_new_bound_factor = %lf choose_dav_bound_factor = %lf, choose_fail_bound_factor = %lf\n",
	dd->davio_exist_factor, dd->choose_lower_bound_factor, dd->choose_new_bound_factor,
	dd->choose_dav_bound_factor, dd->choose_fail_bound_factor);
#ifndef DD_STATS
	result = Cudd_EnableReorderingReporting(dd);
	if (result == 0) {
	(void) fprintf(stderr,
	"Error reported by Cudd_EnableReorderingReporting\n");
	Cudd_Quit(dd);
	return(NULL);
	}
#endif

	return(dd);

} /* end of startCudd */

#if 0
/** 
	@brief Check BKFDD nodes
		1. Check isolated variables.
		2. Check dead nodes.
		3. Check total nodes.
	return 1 if success, otherwise return 0.
*/
static int
CheckBkfddNodes(
	DdManager * dd
)
{
	int kk;
	unsigned int totalNodes, totalDeads, isolatedCount;
	DdNode *p, *next;
	p = next = NULL;
	DdNodePtr *previousP = NULL;
	DdNode *sentinel = &(dd->sentinel);
	totalNodes = 4; // constants
	totalDeads = isolatedCount = 0;
	for (kk = 0; kk < dd->size; kk++) {
		DdNodePtr *nodelist = dd->subtables[kk].nodelist;
		unsigned int slots = dd->subtables[kk].slots;
		unsigned int k;
		for (k = 0; k < slots; k ++) {
			previousP = &(nodelist[k]);
			p = *previousP;
			while (p != sentinel) {
				next = p->next;
				totalNodes ++;
				if (p->ref == 0) {
					totalDeads ++;
				} else {
					*previousP = p;
					previousP = &(p->next);
				}
				p = next;
			}
			*previousP = sentinel;
		}
	}
	for (kk = 0; kk < dd->size; kk ++) {
		p = Cudd_Regular(dd->vars[kk]);
		if (p->ref == 1) {
			isolatedCount ++;
		}
	}
	if (isolatedCount != dd->isolated) {
		printf("CheckBkfddNodes: isolated inconsistent\n");
		return(0);
	}
	if (totalDeads != 0) {
		printf("CheckBkfddNodes: There are dead nodes\n");
		return(0);
	}
	if (totalNodes != dd->keys) {
		printf("CheckBkfddNodes: BKFDD node count inconsistent\n");
		return(0);
	}
	return(1);
} /* end of CheckBkfddNodes */
#endif
