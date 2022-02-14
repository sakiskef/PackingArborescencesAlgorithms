#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <queue>
#include <list>
#include <climits>
#include <ctime>
#include <chrono>
#include <utility>
#include <vector>
#include <bits/stdc++.h>
using namespace std;

#define MAXLINE       100   /* max length of input line */
#define unused		   -1
#define active          1
#define inactive        0

int* edgematrix;



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
int current_Tree = 0; //the current tree that i am processing
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
int *GnextOut;
int * left_traverse;
int * right_traverse;

int *avoid;

//tong structures
int* G1_out;
 int *G1_firstOut ;
 int *G1_nextOut ;
 int*G1_in;
 int*G1_firstIn;
 int*G1_nextIn;
 
 int* G2_out;
 int *G2_firstOut ;
 int *G2_nextOut ;
 int*G2_in;
 int*G2_firstIn;
 int*G2_nextIn;
 
int *positionIn1;
int *positionOut1;
int *positionIn2;
int *positionOut2; 

//Tong
int n_arbors;
int mybranchings;
int *S;
int nextS;
int *vertex_flag;
int *usable;
int  *G;
 int  **T; 
 
//ford
int *Flow;
int *Gadj;
int *Gfirst; 

std::queue <int> myQ; //the queue where we put the labeled edges
std::queue <int> incident_edges_Q;
std::queue <int> joining_edges;


int flag_node1;
int* pathEdge; // path edges
bool* marked;
pair <int, int> edge; // from, to
vector<pair <int, int>> Edges;
//int *Flow; // flow of each edge

// return the origin x of edge (x,y)
inline int edgeFrom(int k) {
	return from[k];
}

// return the target y of edge (x,y)
inline int edgeTo(int k) {
	return to[k];
}

// if v is the origin of the edge k, then return its flow
// otherwise, return 1-flow
inline int edgeFlow(int k, int v) {
	int x = from[k];  // from node
	int y = to[k];  // to node
	int f = Flow[k];  // edge flow

	if (v == x) return f;
	if (v == y) return 1 - f;
	exit(-1); // error!
}

inline void setEdgeFlow(int k, int f) {
	Flow[k] = f;
}

// if v is the origin of the edge k, then return 1-flow
// otherwise, return flow
inline int edgeCapacity(int k, int v) {
	int x = from[k];  // from node
	int y = to[k];  // to node
	int f = Flow[k];  // edge flow

	if (v == x) return 1-f;
	if (v == y) return f;
	exit(-1); // error!
}

// v must be an endpoint of the edge k=(v,w) or k=(w,v). 
// returns w
inline int edgeOther(int k, int v) {
	int x = from[k];  // from node
	int y = to[k];  // to node

	if (v == x) return y;
	if (v == y) return x;
	exit(-1); // error!
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
	//cout<<" i red "<<rline<<" edges"<<endl;
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
	
	//Tong structures
	S = new int[n+2];
    vertex_flag = new int[n+1]; 
	usable = new int[2*m]; 
	
	
	//Ford-Fuljrson
	Flow = new int[m];
	pathEdge = new int[n+1]; // parents in bfs tree
	marked = new bool[n+1];
	Gadj = new int[2 * m];
	Gfirst = new int[n + 2];
	int* Gnext = new int[n + 2];

     for (int i=0; i<n+1; i++){ 
		//S[i] = -1;
		vertex_flag[i] = 0;
	}
	 for (int i=0; i<n+2; i++){ 
		S[i] = -1;
		//vertex_flag[i] = 0;
	}
	nextS = 1;
	
	for (int i = 0; i < 2 * m; i++) Gadj[i] = 0;
	
	

    for (int i=0; i<m; i++){
	
			Gin[i] = Gout[i] = 0;
			positionIn[i] = -1;
			positionOut[i] = -1;	
			from[i] = -1;
			to[i] = -1;	
			//usable[i] = 0;
           	
	
	}
	 for (int i=0; i<2*m; i++){
			
			usable[i] = 0;
           	
	}
    for (int i=0; i<=n+1; i++){ 
		GfirstOut[i] = 0;
		GnextOut[i] = 0;
		GfirstIn[i] = 0;
		GnextIn[i] = 0;
		Gnext[i] = 0;
		Gfirst[i] = 0;
	}

    for (int k=0; k<m; k++)
    {
        x = input_file[2*k];
        y = input_file[2*k+1];
        GfirstOut[x+1]++;
        GfirstIn[y+1]++;
		
		Edges.push_back(make_pair(x, y));
		
		Gfirst[x + 1]++;
		Gfirst[y + 1]++;
    }

    for (int k = 1; k <= n+1; k++) {
	
        GfirstOut[k] += GfirstOut[k-1];
        GnextOut[k] = GfirstOut[k];
        GfirstIn[k] += GfirstIn[k-1];
        GnextIn[k] = GfirstIn[k];
		
		Gfirst[k] += Gfirst[k - 1];
		Gnext[k] = Gfirst[k];
    }

    for (int k = 0; k < m; k++)
    {
		
        x = input_file[2*k];
        y = input_file[2*k+1];
		
		positionIn[GnextIn[y]] = k;
		positionOut[GnextOut[x]] = k;
		
		x = get<0>(Edges[k]);  // from node
		y = get<1>(Edges[k]);  // to node
		Gadj[Gnext[x]++] = k;
		Gadj[Gnext[y]++] = k;
		
			//cout<< k<< " to "<<x<<" -> "<<y<<endl;
		
		
		from[k] = x;
		to[k] = y;
			
        Gout[GnextOut[x]++] = y;
        Gin[GnextIn[y]++] = x;
				 
    }

  //  printGraph(Gout, GfirstOut, n)

    delete [] GnextIn;
    delete [] GnextOut;
	delete [] Gnext;

}

void init(){

	// initilize  variables and data structures

	label2pre = new int[n+1];									// assistant matrix for dfs which labels the nodes while visiting them									//the inverse matrix from the previous
	indegrees = new int[n+1];  									//here we store the current indegree of each node
	forests = new int[n+1];			
	edge_state = new int [m];
	labels     = new int [m];
	edges = new int[m];		
	A_path = new int [m];
	L_roots   = new int [K];
	tree_flag = new int[K];
	labelled  = new int* [K];
	parent = new int* [K];
	parent_edge_id = new int* [K];
	depths = new int* [K]; 
	Gout_T = new int [2*n];
	edges_id = new int [2*n];
    GfirstOut_T = new int [n+2];
    GnextOut = new int [n+2];
	left_traverse = new int[m];
    right_traverse = new int[m];
    root = new int[n+1];
	
	
	//cout<<"bind is ok"<<endl;
	
 
	 for(int i = 0; i <= current_Tree; i++){

		  labelled[i] = new int[n+1];		
		  parent[i] = new int[n+1];
		  parent_edge_id[i] = new int[n + 1];
		  depths[i] = new int[n+1];
	 }

	for (int i = 0; i < m; i++){

		edge_state[i] = -1;			//edge i is unused
		labels[i] = -1;				//edge i is unlabelled
		edges[i] = -1;
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

void update_parents_dfs(int *edges_id, int *Gout_T,int *GfirstOut_T,int t, int k){

	label2pre[k] = 1;
   
	/*update parent and depth values via dfs routine*/
	
   for (int j = GfirstOut_T[k]; j < GfirstOut_T[k+1]; j++) {
   
        int v = Gout_T[j];
        if (!label2pre[v]) {

				mydepths++;
				update_parents_dfs(edges_id, Gout_T, GfirstOut_T, t, v);
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
//	cout<<"2"<<endl;

    for (int k = p1; k < p2; k++)
    {	
	
		e = edges[k];
	
		if (e != -1){
		
			
			x = from[e];
			y = to[e];
		
			//assert(Gout_T[2*n -1]== 0);
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
	update_parents_dfs(edges_id, Gout_T, GfirstOut_T, t, r);
	//cout<<"3"<<endl;
	if (t == current_Tree){
	
		for (int i = 1; i < n + 1; i++){
	
			v = root[i];
			
			if ( root[v]!= v) v = root[v];

			if (label2pre[v] == 0 && v != r){
				mydepths = 0;
				update_parents_dfs(edges_id, Gout_T, GfirstOut_T, t, v);
				
			}
			
			//update vertex labels to the root to the new f-tree
			root[i] = root[v];
		}	
	}
	//cout<<"done"<<endl;
}


void transfer(int Ti, int f){

	/*this function transfers edge f to the tree t*/

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

	if (z1 != z2){				  									 //if the roots are diferrent 

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
			
		if (edge_state[e] == unused){ 
		
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
		
		if (z1 != z2){
		    
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
	//int x1,y1;
	
	for (int i = 0; i< m; i++){
		left_traverse[i] =-1;
		right_traverse[i] = -1;
	}
	
	

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

	if (x == y)														//there is no unlabeled edge in the fundamental cycle
		return -1;
	
	/*start double traverse*/
	
   do {

      while (depths[tree][x] >= depths[tree][y]) { 

		   labelled[tree][x] = 1;
		
			
			q = parent_edge_id[tree][x];
		 
		   if (q == -1){
				cout <<" error  "<<endl;
				exit(-1);
		   }   
		   if ( labels[q] == -1 ){			           		//if the edge is unlabelled

					left_traverse[k1++] = q ;		        //place the edge in left_traverse matrix	
					//cout<<x<<" "<<parent[tree][x]<<" "<<from[q]<<" "<<to[q]<<endl;
					x = parent[tree][x];

					
					if (check_if_joining(q) == 1){			//check if q is joining

						labels[q] = e;
						return q;
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
				cout <<" error "<<q<<endl;		
			    exit(-1);

			}
			if ( labels[q] == -1 ){                     		//if the edge is unllabelled 

					right_traverse[k2++] = q;			        //place the edge in right traverse matrix
					y = parent[tree][y];
						//cout<<"call with "<<from[q]<<" "<<to[q]<<endl;
					if (check_if_joining(q) == 1){				//check if q is joining

						labels[q] = e;
						return q;
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

	
	init_Lroots(x);																	//initialize the L_i tree of  every T_i with the vertex x
	joining_edge = Next_edge_step();												//start cycle_scanning algorithm
	
	if (joining_edge != -1){														//if i found joining edge

		nswaps++;														
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
		
		  
		  if ( t != unused){
		  
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
	 //cout<<"gg"<<endl;
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
int construct_trees(){
 
	/* computing the trees */

	  int z;
	  int njoins = 0;
	   
	   current_Tree = -1;
	//  cout<<"done"<<endl;	
	  init();	
		
  // --- computing  the rest (K - 1)  trees ---//
	for (int j = 0; j < K; j++){

		current_Tree++;												//go for the next tree 	
		njoins = 0;
		increase_memory_for_new_tree();
		// cout<<"done"<<n<<endl;	
		while (njoins < n - 1){
		
			z = choose_root();										//returns the root of an active subtree, or -1, in case of no acive subtree exists.
			
			while (z != -1){
			
				if (search_joining( z ) == 1){						//increase the root z of the coresponding f_tree  if it is possible
				
					njoins++;
					//cout<<njoins<<endl;
				}
				else{												//otherwise halt

					//printf("\n There is %d intersection\n", current_Tree);
					return current_Tree;
				}
				z = choose_root();									//continue untill no active f_tree exists
			}
			
			Augmentation_Algorithm();								//trace out the paths in order to transfer the edges to the appropriate Ti								
			//printTree(0);
			//cin>>z;
			//cout<<"done "<<n<<endl;
			reInit();												//reinit data structures and make all f_trees active for the next
			//cout<<"doneeee"<<endl;	
		}
		//cout<<"tree "<<j+1 <<" is ok "<<endl;	
	}
	return K;
}
void Define_upper_bound_of_K(){

	/*This function assigns K to the minimun degree of some vertex from the graph*/

	int *degrees;
	degrees = new int[ n + 1];
	int min = 0;
	
	degrees[min] = n*5;

	for (int i = 1; i < n + 1 ; i++){
		degrees[i] =  GfirstOut[i+1] - GfirstOut[i] + GfirstIn[i+1] - GfirstIn[i];
		if (degrees[i] < degrees[min]){		
				min = i;	
		}
	}
	
	K = degrees[min] + 1;
	//cout<<"min is "<<K<<endl;
	
	delete [] degrees;
}

/*---------END OF GABOW-----------*/


/*---------FORD AND FULKERSON-----------*/

/* execute a breadth-first search to find a path from s to t */
bool findPath(int s, int t) {

	std::queue <int> q; // bfs queue 
    q.push(s);

	for (int i = 0; i <= n; i++) {
		pathEdge[i] = -1;
		marked[i] = false;
	}
	marked[s] = true;

	while ( (!q.empty()) && (!marked[t]) ) 
    { 
        int u = q.front(); 
        q.pop(); 
        for (int i = Gfirst[u]; i < Gfirst[u + 1]; i++) 
        {
			  int e = Gadj[i];
			  
			if (usable[e] == 0) {
				int k = e;	
				int v = edgeOther(k,u);
				int c = edgeCapacity(k, u);

				if (c > 0) {
					if (!marked[v]) {
						pathEdge[v] = k;
						marked[v] = true;
						q.push(v);
					}
				} 
			}				
        } 
    } 	
	return marked[t];
}

// add 1 unit to the residual flow of edge k 
// if k = (u,v) then flow of k becomes 1
// if k = (v,u) then flow of k becomes 0
inline void addResidualFlowTo(int k, int v)
{
	if (v == to[k]) setEdgeFlow(k, 1);
	if (v == from[k]) setEdgeFlow(k, 0);
}

inline void augmentFlow(int s, int t)
{
	int v = t;
	while (v != s)
	{
		int k = pathEdge[v];
		addResidualFlowTo(k, v);
		v = edgeOther(k, v);
	}	
}

// use FordFulkerson method to compute a flow from s to t of value at most f_max
int FordFulkerson(int s, int t, int f_max){

	if (s == t) return -1;
/*
	pathEdge = new int[n+1]; // parents in bfs tree
	marked = new bool[n+1];*/

	int totalFlow = 0;
	
	// reset all flows 
	for (int k=0; k<m; k++) Flow[k]=0;

	while ( (findPath(s,t)) && (totalFlow <= f_max) ) {
		augmentFlow(s, t); 
		totalFlow++;
		
	}
	
	
	return totalFlow; 
}





/*---------END OF FORD AND FULKERSON-----------*/


int find_edge(){
	
	int e, v;
	
	int index = 1;
	int u = S[index];
	
	while (index <n+1  && u != -1 ){
		
		
		for (int i = Gfirst[u]; i< Gfirst[u+1]; i++){		
			
			e = Gadj[i];
			
			int x = get<0>(Edges[e]);  // from node
			int y = get<1>(Edges[e]);  // to node
						
			v=y;
							
			if (vertex_flag[v] == 0 && usable[e] == 0 && avoid[e]==0){	
			
					return e;
				}
						
		}		
		u = S[++index];
	}
	
	
}



int find_branchings(){
	
	//init_tree();//initialize structures of branching
	
	nextS = 1;
	for (int i = 0; i <n +1; i++){
		S[i] = -1;
		vertex_flag[i] = 	0;
	}
	S[nextS++] = 1;							
	vertex_flag[1] = 1;

	int Con;
	
	int e;
	int i = 1;
	int u,to,from;
	
	avoid = new int [2*m];
	
	for (int i=0;i<2*m;i++){avoid[i]=0;}
	
	while(nextS < n+1 && S[n] == -1){        //while my set does not include all the nodes	
		
		e = find_edge();

		if (e == -1){
			cout<<"error edge not found "<<endl;			
			exit(1);
		}
		else{	
			
			usable[e]=1;
			
			to= get<1>(Edges[e]);
			
			Con = FordFulkerson(r, to, n_arbors);	
						
		}
		if (Con >= n_arbors - mybranchings){	
			u = get<1>(Edges[e]);;		
			S[nextS++] = u;
			usable[e] = 1;
			vertex_flag[u] = 1;
			from=get<0>(Edges[e]);
			edgematrix[u]= from;				  
			}
		else{
				usable[e]=0;			
				avoid[e]=1;
		}
		
	}
	
	/*for (int a = 0; a < n + 1; a++) {			
			cout<<edgematrix[a]<<"--";			
		}
	cout<<endl;*/
		

	for (int w = 0; w < n + 1; w++) {
		edgematrix[w] = 0;
		}
	return 1;
}

void find_dfs_tree(int k){
	

	label2pre[k] = 1;
	
	for (int i = Gfirst[k]; i < Gfirst[k + 1]; i++) 
        {
			  int e = Gadj[i];
			  
			  int x = get<0>(Edges[e]);  // from node
			  int y = get<1>(Edges[e]);  // to node
				 if (x==k){
					//cout<<x<<"->"<<y<<endl;
					
				   int v = y;
					//int e = positionOut[j];
					if (label2pre[v]==0 && usable[e] == 0) {
						edgematrix[v]= k;
						//dfs_edges[myc++]=e;
						find_dfs_tree(v);	
					 }	
				 }
        }	
    
	
}
void compute_dfs_tree(int r){
	 for (int i = 0; i < n+1; i++)  label2pre[i] = 0;
	// cout<<"mesa sto compute"<<endl;
	// myc = 0;
	 find_dfs_tree(r);	 
}

void tarjan(){
	
	int status;
	edgematrix = new int[n + 1];
	
	
	for (int w = 0; w < n + 1; w++) {
		edgematrix[w] = 0;
	}
	
	
	mybranchings = 1;
	
	while (mybranchings < n_arbors){	  
           
		   status = find_branchings();   	 
		   
		   if (status == 1){
			  // cout<<"branching is ready"<<endl;
			   mybranchings++;
			   //cout<<"mybranchings are "<<mybranchings<<endl;
		   }		   
	}
	
	if (mybranchings = n_arbors){
		cout<<"dfs"<<endl;
		compute_dfs_tree(1);
		
	}
	/*for (int a = 0; a < n + 1; a++) {			
			cout<<edgematrix[a]<<"--";			
		}
	cout<<endl;
	 */
}


int main(int argc, char *argv[]){

	using namespace std::chrono;
	 if (argc != 2) {
        printf("\n usage: %s <input file> \n\n", argv[0]);
        exit(-1);
     }

	 char* file = argv[1];
	
	 readGraph(file);			//reading graph from file	
	 processInput();			//building adjancecy lists
	 
	 high_resolution_clock::time_point t3 = high_resolution_clock::now();
	 
	Define_upper_bound_of_K();  //assign K to the min degree 
	
	init();
	//n_arbors = construct_trees();			//main routine
	n_arbors = 8;			//main routine
	cout <<"arbors are "<<n_arbors<<endl;
	
	high_resolution_clock::time_point t4 = high_resolution_clock::now();

	duration<double> time_span1 = duration_cast<duration<double>>(t4 - t3);
	std::cout << "Running time for S-connectivity " << time_span1.count() << " seconds.";
	std::cout << std::endl;
	
	
	high_resolution_clock::time_point t1 = high_resolution_clock::now();
	cout<<"tarjan"<<endl;
	tarjan();
	
	high_resolution_clock::time_point t2 = high_resolution_clock::now();

	duration<double> time_span = duration_cast<duration<double>>(t2 - t1);
	std::cout << "Running time for tarjan " << time_span.count() << " seconds.";
	std::cout << std::endl;

	  
    return 0;
}
