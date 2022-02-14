
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <fstream>
#include <queue>
#include<ctime>
#include <chrono>
#include <assert.h>


#define MAXLINE       100   /* max length of input line */
#define unused		   -1
#define active          1
#define inactive        0


int K;	//the minimun degree of some vertex
int *edge_state; //matrix that shows in which tree the edge is used, or shows that is free for use 
int *labels; //matrix thst shows the label of each edge
int **parent; //the parent of each vertex
int **parent_edge_id;
int *root;	//the label of a vertex  which shows the root_vertex of the f_tree
int **labelled; //This matrix shows if a node is labeled (belongs to Li)

int *label2pre; // mapping node id -> preoder number
int *L_roots;  // the roots ri of L_trees

char line[MAXLINE]; /* stores input line */
int *input_file; // stores input arcs
int n, m; // number of nodes, arcs
int r; // root vertex
int *Gout, *GfirstOut; // adjacency list
int *Gin, *GfirstIn; // reverce adjacency list
int *Gin_target_node; // list which shows the pointed node of an edge
int *Gout_source_node; //list which shows the pointing node of an edge
int depth = 0; //global variable for computing the depth
int mydepths = 0; //global variable for dfs
int *indegrees; //the indegree of each node
int current_Tree; //the current tree that i am processing
int *forests; //matrix that shows if the the f tree is active or inactive
int **depths; //the depths of the nodes in each tree
int * A_path;// returning path of cycle traversal algorithm
int next_f_tree = 1; //indicator of the next f_tree for augmentation
int nswaps = 0; //nymber of swaps
int augmenting_root; // the root which is tested for augmentation
int *tree_flag;
int *edges;
int *positionIn;
int *positionOut;
int *from;
int *to;
int *Gout_T;
int *edges_id;
int *GfirstOut_T;
int * left_traverse;
int * right_traverse;
int **root_set;
int *myset;
int *set_seen;
int sets = 0;
int nexti = 1;
int narbors = 1;
int n_tree;
bool search_mode;
int myc;


std::queue <int> myQ; //the queue where we put the labeled edges
std::queue <int> incident_edges_Q;
std::queue <int> joining_edges;



//for packing
int *Arbor_edge;
int *dfs_edges;
int *A ;
int *inA;
int *inX;
int *marked_edge;


using namespace std;


/* print tree in stdout */
void printTree(int t) {


    fprintf(stdout, "\n");
	fprintf(stdout,"Tree parent node_id\n");
	fprintf(stdout, "\n");


    for (int i = 1; i < n +1; i++) {
				fprintf(stdout, "T%d	%d	%d	%d\n", t + 1, parent[t][i], i,parent_edge_id[t][i]);//, labelled[t][i], root[t][i]);
    }

}
/* print depths in stdout*/
void printDepths(int t){

	cout<<"\n"<<endl;
	fprintf(stdout,"Tree depth node_id\n");
	fprintf(stdout, "\n");


	 for (int i = 1; i <= n; i++) {
        fprintf(stdout, "T%d	%d	%d\n", t + 1, depths[t][i], i);
    }
}

/* print adjacency lists in stdout */
void printGraph(int* nodelist, int* first, int N) {
    printf("Printing adjacency lists\n");
    for (int i=1; i<=N; i++) {
        printf("node %d : ", i);
        for (int j=first[i]; j<first[i+1]; j++) {
            printf("%d", nodelist[j]);
        }
        printf("\n");
    }
}
void printTrees(){

for (int j = 0; j <= current_Tree; j++ )				
		printTree( j );

}
void printDegrees(){


	cout<<"\n\nnode	indegree\n"<<endl;
	for (int j = 1; j < n + 1; j++ )				
		cout<<j<<"	"<<indegrees[j]<<endl;

	cout << "\nswaps are "<<nswaps<<endl;

}
/* read graph from input file */
void readGraph(const char *file) {


	/*  This function reads the graph (input file) and stores the edges in a matrix. */


    FILE *input = fopen(file, "r");
    if (!input) {
        fprintf(stderr, "6Error opening file \"%s\".\n", file);
        exit(-1);
    }

    int x, y;
    int p = 0;
	int l =0;
	int rline = 1;
    while (fgets(line, MAXLINE, input) != NULL) {
        switch (line[0]) {
            case '\n':;
            case '\0':break;
			case '#' :break;
            case 'p': if (sscanf(line, "p %d %d %d", &n, &m, &r) != 3) {
							fprintf(stderr, "5 Error reading graph size (%s).\n", file);
							exit(-1);
						}
						input_file = new int [2*m];
						break;
            default: if (l = sscanf(line, "%d %d", &x, &y) != 2) {
							fprintf(stderr, "2 Error reading graph arc (%s).\n", file);
							cout<<" rline is "<<rline<<endl;
							exit(-1);
					  }
					  input_file[p++] = x;
					  input_file[p++] = y;
					  rline++;
					  if (p>2*m) {
						 fprintf(stderr, "1Error! Graph has >%d arcs.\n", m);
						 cout<<" rline is "<<rline<<endl;
						 exit(-1);
					  }
        }
    }
	cout<<" i red "<<rline<<" edges"<<endl;
    fprintf(stderr, "END reading graph (%s).\n", file);
    fclose(input);
}
void processInput() {

	/* Building adjacency lists from the matrix of edges. */

    int x,y;

    Gout = new int [m];
    GfirstOut = new int [n+2];
    int *GnextOut = new int [n+2];
	
    Gin  = new int [m];
    GfirstIn  = new int [n+2];
    int *GnextIn  = new int [n+2];
	
	positionIn = new int[m];
	positionOut = new int[m];	
	from = new int[m];
	to = new int[m];
	Arbor_edge = new int[m];
	dfs_edges = new int[n];
	
	

    for (int i=0; i < m; i++){
	
			Gin[i] = Gout[i] = 0;
			positionIn[i] = -1;
			positionOut[i] = -1;	
			from[i] = -1;
			to[i] = -1;
            Arbor_edge[i] = -1;			
	}
    for (int i=0; i<=n+1; i++) GfirstOut[i] = GnextOut[i] = GfirstIn[i] = GnextIn[i] = 0;
	for (int i=0; i<n; i++) dfs_edges[i]=-1;

    for (int k=0; k < m; k++)
    {
        x = input_file[2*k];
        y = input_file[2*k+1];
        GfirstOut[x+1]++;
        GfirstIn[y+1]++;
    }

    for (int k = 1; k <= n+1; k++) {
	
        GfirstOut[k] += GfirstOut[k-1];
        GnextOut[k] = GfirstOut[k];
        GfirstIn[k] += GfirstIn[k-1];
        GnextIn[k] = GfirstIn[k];
    }

    for (int k = 0; k < m; k++)
    {
		
        x = input_file[2*k];
        y = input_file[2*k+1];
		
		positionIn[GnextIn[y]] = k;
		positionOut[GnextOut[x]] = k;
		
			//cout<< k<< " to "<<x<<" -> "<<y<<endl;	
		from[k] = x;
		to[k] = y;
	
        Gout[GnextOut[x]++] = y;
        Gin[GnextIn[y]++] = x;
				 
    }
   
  //  printGraph(Gout, GfirstOut, n)

    delete [] GnextIn;
    delete [] GnextOut;

}
void init(int time){

	// initilize  variables and data structures
	current_Tree = 0;
	if (time == 0){

		label2pre = new int[n+1];									
		indegrees = new int[n+1];  									
		forests = new int[n+1];			
		labels     = new int [m];
		edges = new int[m];		
		A_path = new int [m];
		L_roots   = new int [K];
			tree_flag = new int[K];
		labelled  = new int* [K];
		root_set = new int* [n];
		parent = new int* [K];
		parent_edge_id = new int* [K];
		depths = new int* [K]; 
		Gout_T = new int [2*n];
		edges_id = new int [2*n];
		GfirstOut_T = new int [n+2];
		left_traverse = new int[m];
		right_traverse = new int[m];
		root = new int[n+1];
	}
	
	while(!joining_edges.empty()){
		   joining_edges.pop();
	}
	while (!myQ.empty()){
		myQ.pop();
	}		
    while (!incident_edges_Q.empty()){
		incident_edges_Q.pop();	
	}

	
	 for(int i = 0; i <= current_Tree; i++){

		  labelled[i] = new int[n+1];		
		  parent[i] = new int[n+1];
		  parent_edge_id[i] = new int[n + 1];
		  depths[i] = new int[n+1];
	 }

	for (int i = 0; i < m; i++){

		labels[i] = -1;				//edge i is unlabelled
		edges[i] = -1;
		edge_state[i] = -1;		
	}
	for (int i = 0; i <= current_Tree; i++){
			L_roots[i] = -1;
			tree_flag[i] = -1;
		for (int j = 1; j < n+1; j++){ 
			  parent[i][j] = 0;
			  parent_edge_id[i][j] = -1;
		      depths[i][j] = 0; 
			  labelled[i][j] = -1;
			  root[j] = j;
		}
	}
	
    for (int i = 0; i < n+1; i++){

			label2pre[i] = 0;	
			indegrees[i] = 0;
	}
		
	//initialize f_trees in active or inactive mode
	 for (int i = 1; i < n+1; i++){
		if (i != r){
				forests[i] = active;
		}
		else{
				forests[i] = inactive;
		}
	 }
}

 void turn_subtrees_active(){

	 /* Reactivating all the forests for the next round. */
	 int v;
	 for (int i = 1; i < n + 1; i++){
		 v = root[i];
			if (v != r){ 
				forests[v] = active;
			}
	 }
}

int choose_root(){

	/* This function returns the root of an active f_tree. */

	int v;
	for (int i = next_f_tree; i < n+1; i++){
		v = root[i];	
		if (forests[v] == active){
			next_f_tree = i + 1;
			return v;
		}
	}
	return -1;
}
 void join(int j){
 
    /*This function assighns the edge j to the current tree, in other words joins 2 f trees and updates the root of the new f_tree */

	int x = from[j];
	int y = to[j];
	int r1, r2;

	//cout<<" join edge "<<Gin[j]<<" "<<Gin_target_node[j]<<endl;
	
	r1 = root[x];
	r2 = root[y];

	forests[r1] = inactive;	          								// turn the 2 joined f-tree inactive
	forests[r2] = inactive;

	edge_state[j] = current_Tree;

	if (augmenting_root == r2){	
		root[r2] = root[r1];			//update the root of the joined f_tree
	}
	else{
		root[r1] = root[r2];			//update the root of the joined f_tree				
	}
	
	//empty the queue after join
	while (!myQ.empty()) {							
		myQ.pop(); 
	}
}
void update_parents_dfs(int t, int k){

	label2pre[k] = 1; 
	/*update parent and depth values via dfs routine*/
   for (int j = GfirstOut_T[k]; j < GfirstOut_T[k+1]; j++) {
        int v = Gout_T[j];
        if (!label2pre[v]) {

				mydepths++;
				update_parents_dfs(t, v);
				parent[t][v] = k;
				parent_edge_id[t][v] = edges_id[j];
				depths[t][v] = mydepths;
				mydepths--;
        }	
    }		
}
 void update_parents_depths(int t){
	 

	int y;
	int	x;
	int v;

    int * GnextOut = new int [n+2];
	
	//cout<<"updating "<<endl;

	/* This function conctruct an adjancecy list of the tree t and calls dfs routine to update
	   parents and  depths and vertex labels to the root of each f_tree (if we are at tree k). This function is called at the end of a round */

    for (int i = 0; i < 2*n; i++){  
	
		Gout_T[i] = 0;
		edges_id[i] = -1;
	}
    for (int i = 0; i <= n+1; i++){
	
		GfirstOut_T[i] = 0;
		GnextOut[i] = 0;
	}
	int p1 = t*n ;
	int p2 = p1 + n ;
	int e;
	
	
    for (int k = p1; k < p2; k++)
    {
			e = edges[k];
			
			if (e != -1){
			
				x = from[e];
				y = to[e];	
				
				GfirstOut_T[x+1]++;
				GfirstOut_T[y+1]++;
			}			
    }

    for (int k = 1; k <= n+1; k++) {

        GfirstOut_T[k] += GfirstOut_T[k-1];
        GnextOut[k] = GfirstOut_T[k];
			
    }
	

    for (int k = p1; k < p2; k++)
    {	
		e = edges[k];
		if (e != -1){
			x = from[e];
			y = to[e];
		
			edges_id[GnextOut[x]] = e;
			edges_id[GnextOut[y]] = e;
			Gout_T[GnextOut[x]++] = y;
			Gout_T[GnextOut[y]++] = x;		
		}					
    }  
	for (int i = 1; i < n + 1; i++){
	
		depths[t][i] = 0;
		parent[t][i] = 0;
	}
	for (int i = 0; i < n+1; i++)  label2pre[i] = 0;

	
	mydepths = 0;
	update_parents_dfs(t, r);
	
	if (t == current_Tree){
		for (int i = 1; i < n + 1; i++){
			v = root[i];
			
			if ( root[v]!= v) v = root[v];

			if (label2pre[v] == 0 && v != r){
				mydepths = 0;
				update_parents_dfs(t, v);
				
			}		
			//update vertex labels to the root to the new f-tree
			root[i] = root[v];
		}	
	}
	
	delete [] GnextOut;	
}
void transfer(int Ti, int f){
	edge_state[f] = Ti;
}

void trace_back(int joining_edge, int old_state){

	

	/* This function traces out the path of a joining edge and transers the edges to the appropriate Ti. */

	int t;
	int x = to[joining_edge];			/*this is the  node where the joinng edge is pointing*/
	int y = from[joining_edge];						/*thi is the node where the joining edge comes from*/
	int prev_state = -2;								   //here we store the previous state (tree Ti or unused) of an edge
	
	int e = labels[joining_edge];			
	int f = labels[e];
	
	if (e == -1){		
		cout<<"error: joining edge without label"<<endl;
		exit(1);
	}

	/* we have two cases if the joining edge is already used or not*/

		if (old_state == unused ){
		
			 t = edge_state[e];
			 prev_state = edge_state[f];

			 transfer(t, f);
			 edge_state[e] = unused;

			 e = f;
			 f = labels[e];			
		}
		else{

			t = old_state ;
			t++;
			if (t > current_Tree) t = 0;

			 e = joining_edge;
			 f = labels[e];
		}
		
		/*transfer edges to the appropriate Ti*/
		while (f != -2){ 							// -2 indicates the special label of the first edge in the path

		   if (prev_state == unused){
					
				 	t--;
					if (t < 0) t = current_Tree;
					e = f;
					f = labels[e];
		
					prev_state = edge_state[f];
				
					transfer(t, f);
					edge_state[e] = unused;
		
					e = f;
					f = labels[e];
									
			 }
			 else if (prev_state != unused ){

					t--;
				    if (t < 0 ) t = current_Tree;
					prev_state = edge_state[f];
					transfer(t, f);

					e = f;
					f = labels[e];
			 }
		}		
}
int Label_step(int j, int e){

	/* This function labels the edge e withe the label j and tests if the edge is joining or not */


	int x = from[j] ;												// x is the source node of the edge j
	int y = to[j];										// y is the pointing node of the edge j
	int z1 = root[y];									// z1 is the root of y node
	int z2 = root[x];									// z2 is the root of x node 

	labels[j] = e;													//label the edge j with e

	if (z1 != z2 && Arbor_edge[e] == -1){				  									 //if the roots are diferrent 

		if (z1 == augmenting_root ||z2 == augmenting_root){			 //and 1 root is on the our ftree

				return 1;											 //return 1, success 
		}
	}
	else{			
		  myQ.push(j);
	}
	return 0;
}
int any_unused_is_unlabelled(int x){

	/* This function checks if every edge directed to x which is unused, is also unlabeled */
	int e;
	for (int i = GfirstIn[x]; i < GfirstIn[x + 1]; i++){
			e = positionIn[i];		
		if (edge_state[e] == unused && Arbor_edge[e] == -1){ 	
				if (labels[e] != -1){		
					return 0;
				}
				else{					
					incident_edges_Q.push(e);
				}
		}	
	}
	return 1;
}
int Label_A_step(int l, int k){

	int i = 0;
	int g;
	int x;
	int c;
	
	/* This funcrion labels the incident unused edges as the label_A_step of the algorithm */
	
	while( i < k){

		g = A_path[i++];
		
		if (Label_step(g, l) == 1){														//execute the label step with edge g and label l

			return g;
		}
		x = to[g];
		c = any_unused_is_unlabelled(x);
		if ( c == 1){											// this function checks if every unused edge is also unlabeled

			int edge;
			while( !incident_edges_Q.empty() ){			
					
				edge = incident_edges_Q.front();
				incident_edges_Q.pop();
				
				if ( edge != g ){		//for each unused and unlabelled edge j label the edge j with g
					if (Label_step(edge, g) == 1){
					          
								while(!incident_edges_Q.empty()){
									incident_edges_Q.pop();
								}							 
							    return edge;
					}
				}
			}		
		}		
	}
	while(!incident_edges_Q.empty()){	
			incident_edges_Q.pop();
	}	
	return -1;
}
int check_if_joining(int j){


	// this function checks if j edge is joinng
	int x = from[j];
	int y = to[j];
	int z1 = root[y];
	int z2 = root[x]; 
	
	if (z1 == augmenting_root || z2 == augmenting_root){
		
		if (z1 != z2 && Arbor_edge[j] == -1){
		    
			return 1;
		}
	}
	return 0;
}
int fundamental_cycle_step(int e, int tree){

	/* Do a double traverse from v1 and v2 and build A_path */

	int x = to[e];
	int y = from[e];
	int k1 = 0;
	int k2 = 0;
	bool stop = 0;
	int q;
	int side = 0;
	int x1,y1;
	int s;
	

	
	if (labelled[tree][x] == -1 && labelled[tree][y] == -1){		//we have an error 2 nodes unlabelled and Li exists

			cout<<"error labelling"<<endl;
			exit(-1);		
	}
	if (labelled[tree][x] == 1 ){									//if the node x is labelled go to the root of Li

			x = L_roots[tree];
			side = 1; 
	}
	if (labelled[tree][y] == 1){									// if the node y is labelled go to the root of Li
	
			 y = L_roots[tree];
			 side = 2;
	}
	
	if (search_mode == true){
		s = myset[x];
	
		if (s == -1){
		
			myset[x] = sets;
		
		}
		else {
		
			if (root_set[s][tree] != -1 && s != sets){
				x = root_set[s][tree];
				set_seen[s] = 1;
			}
		}
		s = myset[y];
		if (s == -1){
		
			myset[y] = sets;
		
		}	
		else{
		
			if (root_set[s][tree] != -1 && s!=sets){
				y = root_set[s][tree];
				set_seen[s] = 1;
			}
		}		
	}
	if (x == y)														//there is no unlabeled edge in the fundamental cycle
		return -1;
	
	/*start double traverse*/
	
   do {

      while (depths[tree][x] >= depths[tree][y]) { 

		   labelled[tree][x] = 1;
		   	
			q = parent_edge_id[tree][x];
			
		 
		   if (q == -1){
				cout <<" error 1 "<<endl;
				//printTrees();
				exit(-1);
		   }   
		   if ( labels[q] == -1 ){			           		//if the edge is unlabelled
				
					left_traverse[k1++] = q ;		        //place the edge in left_traverse matrix	
					
					if (check_if_joining(q) == 1){			//check if q is joining

						labels[q] = e;
						return q;
					}
					
					x = parent[tree][x];
					
					if (search_mode == true){
						s = myset[x];
						if (s == -1){
						
							myset[x] = sets;
						}
						else{
		
							if (root_set[s][tree] != -1 && s!=sets){
								y = root_set[s][tree];
								set_seen[s] = 1;
							}
						}
					}
													
			}
		    else if ( labels[q] != -1){			       		//if the edge is labelled stop
			    	
				stop = 1;
				break;
			}
			
			if (x == y) break;		
	 }
	while (depths[tree][y] > depths[tree][x]) {

		   labelled[tree][y] = 1;

		   	q = parent_edge_id[tree][y];
		

		    if (q == -1){ 	
				cout <<" error 2 "<<q<<endl;
				//printTrees();
			    exit(-1);

			}
			if ( labels[q] == -1 ){                     		//if the edge is unllabelled 

					right_traverse[k2++] = q;			        //place the edge in right traverse matrix
				
					if (check_if_joining(q) == 1){				//check if q is joining

						labels[q] = e;
						return q;
					}
					
					y = parent[tree][y];
					
					if (search_mode == true){
						s = myset[y];
					
						if (s == -1){
						
							myset[y] = sets;
						}
						else{
		
							if (root_set[s][tree] != -1 && s!=sets){
								y = root_set[s][tree];
								set_seen[s] = 1;
							}
						}
					}								
			 }
			 else if ( labels[q] != -1){			    		//if the edge is labelled stop
				
				  stop = 1;
				  break;										
			 }
	  }
   } while (x != y && stop == 0);

	
	if (x == y){   												//update the L_root of the tree

		L_roots[tree] = x;
		labelled[tree][x] = 1;
		
	}
   // ---- compute A_path-----  place the edges in a consistency order for the next labeling.
   int i = 0;

   if ( side == 1){
   
		while( i < k1){

			A_path[i] = left_traverse[i];
			i++;
		}
		k2 --;
		while( k2 >= 0){

			A_path[i] = right_traverse[k2];
			i++;
			k2--;
		}
   }
   else if (side == 2){
	    
		while( i < k2){

			A_path[i] = right_traverse[i];
			i++;
		}
		k1--;
		while( k1 >= 0){

			A_path[i] = left_traverse[k1];
			i++;
			k1--;
		}
   }  

   
   /*go to label the A_path*/
   int res = Label_A_step(e, i);
   return res; 
}
int Next_edge_step(){


	/* This function picks up the edges from the queue and starts the labeling untill the queue 
	   becomes empty or a joining edge being found */

	    int myedge;
		int found_joining;
		int i = 0;
	

		while(!myQ.empty()){

			myedge = myQ.front();													//extract  the first element(edge) from the queue
		    myQ.pop();

			 if (edge_state[myedge] == i){											//if e is on Ti, i++
					i++;
				if (i > current_Tree) i = 0;
					
			 }
			 tree_flag[i] = 1;
			 
		    if ((found_joining = fundamental_cycle_step( myedge, i)) != -1){		// find the fundamental cycle of myedge in Ti 

				return found_joining;
			}
		 }

	return -1;
}
void init_Lroots(int x){
	
	/*This function initialize Li trees of each Ti to x node and turns node x labelled*/

	for (int i = 0; i <= current_Tree; i++){
			L_roots[i] = x;
			labelled[i][x] = 1;				
	}
}
void Empty_the_queue(){

	/*This function emptys the queue*/

	int f;
	
	while (!myQ.empty()) {								
	
		f = myQ.front();
			labels[f] = -1;
			myQ.pop(); 
	}
}
int search_joining(int x){

	/* This function tries to grow the f_tree rooted at x */

	int y;
	int joining_edge;														
    int e;
	augmenting_root = x;															//global variable that shows which vertex is about to be increased
	
	for (int j = GfirstIn[x]; j < GfirstIn[x+1]; j++){								//look on the incoming arcs
	
			e = positionIn[j];
			y = from[e];
			y = root[y];															//find the root of the f-tree
	
			if (edge_state[e] == unused){											//if the edge is available	
				
					if ( x != y){													//and the f-trees have diferrent root
						Empty_the_queue();
						join(e);										            //assign the edge j to the current_tree (easy case)		
						return 1;
					}
					else{														    //if the f trees have the same root(cycle) 
																				//add the edge in the queue
						 labels[e] = - 2;											//label the edge with (-2) sign that indicates the first edge of the path 
						 myQ.push(e);		
					}
			}		
	}
	// if i did not find free joining edge, i go to see if i can have one via a sequence of swaps.

															//global variable that shows which vertex is about to be increased
	init_Lroots(x);																	//initialize the L_i tree of  every T_i with the vertex x
	joining_edge = Next_edge_step();												//start cycle_scanning algorithm
	if (joining_edge != -1){														//if i found joining edge
															
		joining_edges.push(joining_edge);
		joining_edges.push(edge_state[joining_edge]);
									

		join( joining_edge);										    			// join the two subtrees
		return 1;
	}
	return 0;
}
void order_edges_from_trees(){


	/* This function orders the edges acoording to the tree so we can update faster at the end of the round*/

	int trees = current_Tree + 1;
	int *next_tree = new int[trees + 1];
	
	
	for (int i = 0; i < trees;  i++){
	
		next_tree[i] = i*n;
		
	}
	int t;
	
	for (int k = 0; k < m; k++){
	
	      t = edge_state[k];
		
		  
		  if ( t != unused && t!= -2){
		  
				edges[next_tree[t]++] = k;		  
		  }
	}
		
	delete[] next_tree;	
}
void reInit(){


	/* This function turns the f_trees active (except the root), updates depths and parents values  and clears the labels,
       this function is callesd at the end of a round	*/


	 turn_subtrees_active(); 
	 order_edges_from_trees();
	  
	 /*update parent and depth values*/	
	for (int j = 0; j <= current_Tree; j++ ){
	
	    	if (tree_flag[j] == 1 || j == current_Tree || j == 0){
			   
				update_parents_depths( j );
			}
	}
	 for (int j = 0; j <= current_Tree; j++){
	 
		L_roots[j] = -1;								//clear roots of every L_i
		tree_flag[j]= -1;
		for (int i = 1; i < n+1; i++){  
		
			labelled[j][i] = -1; 						//all nodes from every Ti are becoming unlabelled
		}
	}		
	for (int i = 0; i < m; i++)  edges[i] = labels[i] = -1;		//clear the label of every edge
	  
	next_f_tree = 1;
 	
}

void Augmentation_Algorithm(){

/* This function traces out the paths of the found joining edges*/



	int i = 0;
    int e,s;
	while(!joining_edges.empty()){
	
		e = joining_edges.front();													//extract  the first element(edge) from the queue
		    joining_edges.pop();
			
		s =	joining_edges.front();													//extract  the first element(edge) from the queue
		    joining_edges.pop();
		trace_back(e, s);

	}
}
void increase_memory_for_new_tree(){

/*this function increases the memory which is for a new tree*/

     labelled[current_Tree] = new int[n + 1];		
	 parent[current_Tree] = new int[n + 1];
	 depths[current_Tree] = new int[n + 1];
	
	 parent_edge_id[current_Tree] = new int[n +1];

	for (int j = 1; j < n + 1; j++){
	 		
		parent[current_Tree][j] = 0;
		depths[current_Tree][j] = 0;
		labelled[current_Tree][j] = -1;
		parent_edge_id[current_Tree][j] = -1;
		root[j] = j;
	}	
	
	L_roots[current_Tree] = -1;
	tree_flag[current_Tree] = -1;
		
}	  
int construct_trees(int time){
 
	/* computing the trees */

	  int z;
	  int njoins = 0;
	  int j;
	  init(time);														//initalizing variables and data structures
	  
	  current_Tree = -1;												// we are in tree 1
	 		 								  
    
  // --- computing  the rest (K - 1)  trees ---//
	for (j = 0; j < K; j++){

		current_Tree++;												//go for the next tree 	
		njoins = 0;
		increase_memory_for_new_tree();
		 
		while (njoins < n - 1){

			z = choose_root();										//returns the root of an active subtree, or -1, in case of no acive subtree exists.
				 
			while (z != -1){
			
				if (search_joining( z ) == 1){						//increase the root z of the coresponding f_tree  if it is possible
					njoins++;
					//cout<<njoins<<endl;
				}
				else{												//otherwise halt
					return current_Tree;
				}
				z = choose_root();									//continue untill no active f_tree exists
			}
			Augmentation_Algorithm();								//trace out the paths in order to transfer the edges to the appropriate Ti								
			reInit();												//reinit data structures and make all f_trees active for the next	
		}
		//cout<<"tree "<<j+1 <<" is ok "<<endl;	
	}
		
	
	return current_Tree + 1;
}
void Define_upper_bound_of_K(){

	/*This function assigns K to the minimun degree of some vertex from the graph*/

	int *degrees;
	degrees = new int[ n + 1];
	int min = 0;
	
	degrees[min] = n*n;

	for (int i = 1; i < n + 1 ; i++){
		degrees[i] = 0;
		for (int j = GfirstOut[i]; j < GfirstOut[i+1]; j++){
				degrees[i]++;
		}
		if (degrees[i] < degrees[min]){	
				min = i;
		}
	}
	K = degrees[min] + 1;
	delete [] degrees;
}
/* Functions for packing */

 void update_mytree(int t,int k, int l){
	 

	int y;
	int	x;
	int v;
	int e;
	int ne = 0;
	int myv;
	
	int *myedges = new int[n];
    int * GnextOut = new int [n+2];
	
	if (parent[t][k] == l){	
			myv = k;
	}
    else{	
			myv = l;
	}
	for (int i = 0; i < n; i++){  
	
		myedges[i] = -1;
	 }
    for (int i = 0; i < 2*n; i++){  
	
		Gout_T[i] = 0;
		edges_id[i] = -1;
	}
    for (int i = 0; i <= n+1; i++){
	
		GfirstOut_T[i] = 0;
		GnextOut[i] = 0;
	}
	for (int k = 0; k < m; k++){
	
		if (edge_state[k] == t){
		
				myedges[ne++] = k;
		}
	}
    for (int k = 0; k < ne; k++)
    {
			
		   e = myedges[k]; 
			
			x = from[e];
			y = to[e];	
				
			GfirstOut_T[x+1]++;
			GfirstOut_T[y+1]++;					
    }
    for (int k = 1; k <= n+1; k++) {

        GfirstOut_T[k] += GfirstOut_T[k-1];
        GnextOut[k] = GfirstOut_T[k];
			
    }
	
    for (int k = 0; k < ne; k++)
    {	
		    e = myedges[k];
		
			x = from[e];
			y = to[e];
		
			edges_id[GnextOut[x]] = e;
			edges_id[GnextOut[y]] = e;
			Gout_T[GnextOut[x]++] = y;
			Gout_T[GnextOut[y]++] = x;						
    }  
	for (int i = 1; i < n + 1; i++){
	
		depths[t][i] = 0;
		parent[t][i] = 0;
	}
	for (int i = 0; i < n+1; i++)  label2pre[i] = 0;

	
	mydepths = 0;
	update_parents_dfs( t, r);
	
	
	for (int i = 1; i < n+1; i++){  
	
		if (label2pre[i] == 0){
		
			root[i] = myv;
		
		}
		else{	
			root[i] = r;	
		}		
	}	
	mydepths = 0;
	update_parents_dfs(t, myv);
	
	 delete [] myedges;
     delete [] GnextOut;

}
 void packing_join(int j, int tree){
 
   
	int x = from[j];
	int y = to[j];
	int r1, r2;

	r1 = root[x];
	r2 = root[y];

	edge_state[j] = tree;
		root[r2] = r;			
		root[r1] = r;			
	
	//empty the queue after join
	while (!myQ.empty()) {							
		myQ.pop(); 
	}
}
int search_packing_joining( int x, int tree){

	int y;
	int joining_edge;														
    int e;
	augmenting_root = root[x];

	for (int j = GfirstIn[x]; j < GfirstIn[x+1]; j++){								
	
			e = positionIn[j];
			y = from[e];
			y = root[y];															
	
			if (edge_state[e] == unused && Arbor_edge[e] == -1){
						
					
					if ( root[x] != y){													

						Empty_the_queue();
						packing_join(e, tree);
						tree_flag[tree] = 1;
						return 1;
					}
					else{														    
						 labels[e] = - 2;
						 myQ.push(e);												
					}
			}		
	}
	init_Lroots(x);	
	joining_edge = Next_edge_step();	
    	

	if (joining_edge != -1){													
		joining_edges.push(joining_edge);
		joining_edges.push(edge_state[joining_edge]);							
		packing_join( joining_edge, tree);	
		return 1;
	}
	return 0;	
}
void clear_data_structures(){

	 for (int j = 0; j <= current_Tree; j++){
	 
		L_roots[j] = -1;								//clear roots of every L_i
		tree_flag[j]= -1;
		for (int i = 1; i < n+1; i++){  
		
			labelled[j][i] = -1; 						//all nodes from every Ti are becoming unlabelled
		}
	}		
   for (int i = 0; i < m; i++)  edges[i] = labels[i] = -1;	
}
int search_step(int e){


 int x, y, tree, found;
 int *myparent = new int[n+1]; 
 int *mydepth  = new int [n+1];
 
  x = from[e];
  y = to[e];
  tree = edge_state[e];
  tree_flag[tree] = 1;
  
   for (int i = 1; i < n+1; i++){
 
		myparent[i] = parent[tree][i];
		mydepth[i]  = depths[tree][i];
	}
  
  edge_state[e] = -2; //temporary unuused
 
  update_mytree(tree, x, y);
    
  found = search_packing_joining(y,tree);

  if (found == 1){
		
		Augmentation_Algorithm();
		reInit();
		//cout<<"successful search"<<endl;
		delete [] myparent;
		delete [] mydepth;	
		return 1;
  }
  else{
	
      edge_state[e] = tree;
	  //cout<<"unsuccessfuk search"<<endl;
		
	  for (int i = 1; i < n+1; i++){
 
		 parent[tree][i] = myparent[i];
		 depths[tree][i] = mydepth[i];
	 }   
	  clear_data_structures();  
	     
		for (int i = 1; i < n+1; i++){
	
			if (root[i] != r) root[i] = r;	
		}
		delete [] myparent;
		delete [] mydepth;
		 
	  return 0;  
  } 
}

int choose_edge_step(int v){


/* find an edge to augment A if it is possible */

  int e;
  int flag = 0;
  int x;
  std::queue <int> du_da;
  
	for (int j = GfirstOut[v]; j < GfirstOut[v + 1]; j++){  //for all outgoing edges of v

		e = positionOut[j];
        x = to[e];
			
		if ( inA[x] == 0){						//if they are not in A, 		

				du_da.push(e);											//push them in th queue		
		}			
	}
	
	while(!du_da.empty()){
	
		flag = 1;
		e = du_da.front();
		du_da.pop();
		
		if (marked_edge[e] == -1){
			
			flag = 2;
			break;
		}			
	}
	if (flag == 1 || flag == 0){//gia to flag ison 0 to evala egw
	
		return -1;
	}
	else if (flag == 2){
	
			if (edge_state[e] == -1){
					
					Arbor_edge[e] = 1;
					A[nexti++] = to[e];
					inA[to[e]] = 1;
					return -2;
			}
			else{
					
					return e;
			}	
	}
	
	cout <<"undefined flag"<<endl;
	exit(-1);
}
void init_set(){
	
	if (sets != 0){
		for (int i = 0; i< sets;i++) delete [] root_set[i];  //delete previous sets
		sets = 0; //name of the new set	
	}
	root_set[sets] = new int[K];
	
	for (int i = 0; i <  K; i++){
	 
		root_set[sets][i] = -1;	 	 
	}
	for (int i = 0; i < n+1; i++){
	 
		myset[i] = -1;	
		set_seen[i] = 0;	 	 
	}
}
int  period_step(){

/* if the arborescence is ready halt, else return a vertex v from A*/

  int v;
  int i = 1;
   
  init_set();

  if ( A[n] == 0){		//not all nodes in A
  
		v = A[i]; 		
		while (inX[v] != 0){
		
			v = A[++i];
		}
		//cout<<"select from A node "<<v<<endl;
		if (v!=0){
			
			return v;
		}
		else{
			
			cout<<"wrong in period step"<<endl;
		//	printTrees();
			for (int i = 0; i<m; i++){
				
				if (edge_state[i] == -1 && to[i]==3){
					
					cout<<from[i]<<" "<<to[i]<<endl;
				}
			}
			exit(-1);
		}
  }
  else{
  
		nexti = 2;	
		return 0;		
  }  
}

void merge_sets(){
	
		if (sets != 0){		
			for (int i = 1; i < n + 1; i++){		
				int s = myset[i];	
				if ( s != -1 && set_seen[s] == 1){			
						myset[i] = sets; 						
				}
			}						
		}	
		for (int i = 0; i < K; i++){
			root_set[sets][i] = L_roots[i];
		}
		for (int i = 0; i < n+1; i++){
			set_seen[i] = 0;
		}					
		sets++;
		root_set[sets] = new int[K]; 
		for (int i = 0; i < K; i++){

			root_set[sets][i] = -1;
		}		
}
void find_tree(){

	 int found;
	 int e;
	 int success;
	 int v;
	 
   search_mode = true;
  
	for (int i = 0; i < n + 1; i++){	 
		inA[i] = A[i] = inX[i] = 0;	 
	}
	for (int i = 0; i < m; i++){
		marked_edge[i] = -1;	
	}
	 	 
    A[1] = r;     							//first element of the arborescence is the root
    inA[1] = 1;

    v = A[1];
    nexti = 2;
	
	init_set();
	
 
    while(v != 0){
		
		found = choose_edge_step(v);
		
		if (found == -2){					//epistrofi epitixias auksisame to A
	 
			v = period_step();
		}
		else if (found == -1){
	 
			inX[v] = 1;						 //o V komvos exei oles tis akmes tou markarismenes opote epilegoume alon komvo sto period step
			v = period_step();
		}
		else{
	 
			e = found;					    //epistrefetai akmi pou aniki sto T intersection			
			success = search_step(e); 	    //paw na anazitisw joining akmi wste na diatirisw to T	
			if (success == 0){
				
				merge_sets();
				marked_edge[e] = 1; 	    	
			}
			else{
											//alliws thn prosthetw sto A 
				Arbor_edge[e] = 1;
				A[nexti++] = to[e];
				inA[to[e]] = 1;		
				v = period_step();			
			}	 
		}	
	}	
	//cout<<"Arborescence "<<narbors++<<" is ready"<<endl;
	search_mode = false;
}
void G_minus_A(){


	//remove the edges of the tree from the graph

	int x,y;
    int *GnextOut = new int [n+2];
    int *GnextIn  = new int [n+2];

    for (int i=0; i < m; i++){
	
			Gin[i] = Gout[i] = 0;
			positionIn[i] = -1;
			positionOut[i] = -1;	
	}
    for (int i=0; i<=n+1; i++) GfirstOut[i] = GnextOut[i] = GfirstIn[i] = GnextIn[i] = 0;

    for (int k=0; k < m; k++)
    {
	
	   if (Arbor_edge[k] == -1){
	   
			x = input_file[2*k];
			y = input_file[2*k+1];
			GfirstOut[x+1]++;
			GfirstIn[y+1]++;
		}
    }

    for (int k = 1; k <= n+1; k++) {
	
        GfirstOut[k] += GfirstOut[k-1];
        GnextOut[k] = GfirstOut[k];
        GfirstIn[k] += GfirstIn[k-1];
        GnextIn[k] = GfirstIn[k];
    }

    for (int k = 0; k < m; k++)
    {
	
		if (Arbor_edge[k] == -1){
		
			x = input_file[2*k];
			y = input_file[2*k+1];
		
			positionIn[GnextIn[y]] = k;
			positionOut[GnextOut[x]] = k;
		
			Gout[GnextOut[x]++] = y;
			Gin[GnextIn[y]++] = x;
		}				 
    }
	
    delete [] GnextIn;
    delete [] GnextOut;
}
void remove_unused_edges_from_G(){

	int x,y;
    int *GnextOut = new int [n+2];
    int *GnextIn  = new int [n+2];

    for (int i=0; i < m; i++){
	
			Gin[i] = Gout[i] = 0;
			positionIn[i] = -1;
			positionOut[i] = -1;	
           
	}
    for (int i=0; i<=n+1; i++) GfirstOut[i] = GnextOut[i] = GfirstIn[i] = GnextIn[i] = 0;

    for (int k=0; k < m; k++)
    {
	   if (edge_state[k] != -1){
			
			x = input_file[2*k];
			y = input_file[2*k+1];
			GfirstOut[x+1]++;
			GfirstIn[y+1]++;
		}
    }

    for (int k = 1; k <= n+1; k++) {
	
        GfirstOut[k] += GfirstOut[k-1];
        GnextOut[k] = GfirstOut[k];
        GfirstIn[k] += GfirstIn[k-1];
        GnextIn[k] = GfirstIn[k];
    }

    for (int k = 0; k < m; k++)
    {
	
		if (edge_state[k] != -1){
		
			x = input_file[2*k];
			y = input_file[2*k+1];
		
			positionIn[GnextIn[y]] = k;
			positionOut[GnextOut[x]] = k;
		
			Gout[GnextOut[x]++] = y;
			Gin[GnextIn[y]++] = x;
		}
				 
    }
   
    delete [] GnextIn;
    delete [] GnextOut;
	
}
void init_mydata(){
	
	   A = new int[n + 1];
    inX = new int[n + 1];
	inA = new int[n + 1];
	marked_edge = new int[m];
    edge_state = new int [m];
    myset = new int[n+1]; 
    set_seen = new int [n+1];
	search_mode = false;	
}

void find_dfs_tree(int k){
	
	
		label2pre[k] = 1;
   
	/*update parent and depth values via dfs routine*/
	
   for (int j = GfirstOut[k]; j < GfirstOut[k+1]; j++) {
        
        int v = Gout[j];
		int e = positionOut[j];
        if (label2pre[v]==0 && edge_state[e] == unused) {
				Arbor_edge[e] = 1;
				dfs_edges[myc++]=e;
				find_dfs_tree(v);		
        }	
    }	
}
void compute_dfs_tree(int r){
	 for (int i = 0; i < n+1; i++)  label2pre[i] = 0;
	 myc = 0;
	 find_dfs_tree(r);	 
}
void release_used_edges(){	
	for (int i = 0; i < m; i++){	
		edge_state[i] = unused;
	}	
}
void packing_arborescences(){


   int ntrees;
   int temp;
  
   init_mydata();
   ntrees = construct_trees(0);					//find the value of K - intersection 
   K = ntrees - 1;
   if (ntrees == 0){   
	   cout<<" Does not exist any arborescence"<<endl;   
	   exit(1);
   }
   remove_unused_edges_from_G();				//remove unused edges from the graph ( Include only E(T) )
    release_used_edges();
 
   while(1){
	  
	  compute_dfs_tree(r);							//find a tree with dfs 
	  G_minus_A();										//remove the edges of the tree from the graph 
	  temp = construct_trees(1);                  		//compute the connectivity after removing the dfs tree  

		if (temp < ntrees - 1){							// BAD CASE (i did not find good dfs tree)
			 cout<<"BAD CASE"<<endl;
			  cout<<"temp is "<<temp<<endl;
			for (int i=0; i<n;i++){					//turn back the edges
				int e = dfs_edges[i];
				if (e != -1){
					Arbor_edge[e] =-1;
					dfs_edges[i] = -1;    					
				}			
			}
			G_minus_A();
			temp = construct_trees(1);	            //construct a (k-1)  intersection
			 //release_used_edges();
			find_tree(); 
			G_minus_A();
		}
		else{							// GOOD CASE (i found good dfs_tree)	
             cout<<"GOOD CASE"<<endl;				
			for (int i=0; i<n;i++){	
				dfs_edges[i] = -1;
			}	
		}												
		if (K == 0){								// if k = 1, halt, else decrease k by one and reapeat the entire procedure on G-A
		    cout<<"arborescence "<<narbors++<<" is ready"<<endl;
			cout<<"packing done "<<endl;
			break;	 
		}
		else{
			cout<<"arborescence "<<narbors++<<" is ready"<<endl;
			K--;
			ntrees--;      		
		}
  }
}
int main(int argc, char *argv[]){


	 if (argc != 2) {
        printf("\n usage: %s <input file> \n\n", argv[0]);
        exit(-1);
     }

	 char* file = argv[1];

	 readGraph(file);			//reading graph from file
	 processInput();			//building adjancecy lists
	
	Define_upper_bound_of_K();  //assign K to the min degree 
   
   
	
	using namespace std::chrono;
	high_resolution_clock::time_point t1 = high_resolution_clock::now();
	
	packing_arborescences();
	
	high_resolution_clock::time_point t2 = high_resolution_clock::now();

	duration<double> time_span = duration_cast<duration<double>>(t2 - t1);
	std::cout << "Running time " << time_span.count() << " seconds.";
	std::cout << std::endl;
	  
    return 0;
}

