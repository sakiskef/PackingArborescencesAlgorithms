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


int myname = 0;
int mytime = 0;
int K;	//the minimun degree of some vertex
int *edge_state; //matrix that shows in which tree the edge is used, or shows that is free for use 
int *labels; //matrix thst shows the label of each edge
int **parent; //the parent of each vertex
int **parent_edge_id;
int *root;	//the label of a vertex  which shows the root_vertex of the f_tree
int **labelled; //This matrix shows if a node is labeled (belongs Gto Li)

int *label2pre; // mapping node id -> preoder number
int *L_roots;  // the roots ri of L_trees

char line[MAXLINE]; /* stores input line */
int *input_file; // stores input arcs
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
int *Gout_T;
int *edges_id;
int *GfirstOut_T;
int *GnextOut;
int * left_traverse;
int * right_traverse;
int n_splits = 0;

int global_m;
int global_n;




std::queue <int> myQ; //the queue where we put the labeled edges
std::queue <int> incident_edges_Q;
std::queue <int> joining_edges;

//global variables
int n, m, r;
int *Gfrom;
int *Gto;
int idGraph;

using namespace std;

class Graph {      
  public:             
    int n;        					  //number of vertices
	int m;							  //number of edges
	int r;
    int *positionOut;           //id of an edge 
	int *edges;					  //edges of the new graph
	int *edgesID;               //id of the edges 
	int *vertices;                //vertices of the new graph 
	int **T;							//branchings of the graph
	int *Gout;                   
	int *GfirstOut;
	int *Gin;
	int *GfirstIn;
	int *positionIn;
	int *S;							//set of vertices in T
	int *vertex_flag;     	//a flag indicating if a vertex is in S;
	int nextS;				    //global variable showing the next available position in S
	int mybranchings;     //number of my branchings 
	int nextbranching;
	int *inS;						//set of vertices in S after splitting
	int *isT;
	int *Tedge;
	int level;
	Graph *G1;				//pointer to the first subgraph after splitting
	Graph *G2;				//pointer to the second subgraph after splitting
	
	int *usable;
    int *Gadj;
    int *Gfirst;
    int *from;
    int *to;
    int *Flow;
    int* pathEdge; 
    bool* marked;
	
	
	 void BuildGraph();
	 void init_tree(int i, int call);
	 void find_branchings(int index);
	 void printGraph(int n);
	    int find_edge(int x);	 
	 void GgetValues(int x, int y, int z);
     int passing_paremetersG1( Graph *nextGraph);
     int passing_paremetersG2( Graph *nextGraph);
     void combine(int splitted_edge);
     void merge_branchings(int b1, int b2, int Branching, int e);	 
	 void createGadj(int *from,int *to);
	 void computeS();
	 void split(int e, int i, int j);
	 void printBranchings(int next);
	 
	 //ford-fulkerson functions
      int FordFulkerson(int s, int t, int f_max); 
	  inline int edgeFrom(int k) ;
      inline int edgeTo(int k); 
      inline int edgeFlow(int k, int v) ;
      inline void setEdgeFlow(int k, int f) ;
      inline int edgeCapacity(int k, int v) ;
      inline int edgeOther(int k, int v) ;
      bool findPath(int s, int t) ;
      inline void addResidualFlowTo(int k, int v);
      inline void augmentFlow(int s, int t);
};

//--------------GABOW----------------------//
void init(){

	// initilize  variables and data structures

	label2pre = new int[n+1];									// assistant matrix for dfs which labels the nodes while visiting them									//the inverse matrix Gfrom the previous
	indegrees = new int[n+1];  									//here we store the current indegree of each node
	forests = new int[n+1];			
	edge_state = new int [m];
	labels     = new int [m];
	edges = new int[K*n];		
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
	
 
	 for(int i = 0; i <= current_Tree; i++){

		  labelled[i] = new int[n+1];		
		  parent[i] = new int[n+1];
		  parent_edge_id[i] = new int[n + 1];
		  depths[i] = new int[n+1];
	 }

	for (int i = 0; i < m; i++){

		edge_state[i] = -1;			//edge i is unused
		labels[i] = -1;				//edge i is unlabelled
	}
	for (int i = 0; i < K*n; i++){
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
 int v;
for (int i = 1; i < n + 1; i++){
		 v = root[i];
			if (v != r){ 
				forests[v] = active;
			}
	 }
}
int choose_root(){
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
	int x = Gfrom[j];
	int y = Gto[j];
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
			
				x = Gfrom[e];
				y = Gto[e];	
				
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
			x = Gfrom[e];
			y = Gto[e];	
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
			//update vertex labels Gto the root Gto the new f-tree
			root[i] = root[v];
		}	
	}
	//cout<<"done"<<endl;
}
void transfer(int Ti, int f){
	edge_state[f] = Ti;	
}
void trace_back(int joining_edge, int old_state){
	int t;
	int x = Gto[joining_edge];			
	int y = Gfrom[joining_edge];						
	int prev_state = -2;								 
	int e = labels[joining_edge];			
	int f = labels[e];
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

	int x = Gfrom[j] ;												// x is the source node of the edge j
	int y = Gto[j];										// y is the pointing node of the edge j
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
		
	while( i < k){

		g = A_path[i++];
		
		if (Label_step(g, l) == 1){														//execute the label step with edge g and label l

			return g;
		}
		x = Gto[g];
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
	int x = Gfrom[j];
	int y = Gto[j];
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
	int x = Gto[e];
	int y = Gfrom[e];
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
	if (labelled[tree][x] == 1 ){									//if the node x is labelled go Gto the root of Li

			x = L_roots[tree];
			side = 1; 
	}
	if (labelled[tree][y] == 1){									// if the node y is labelled go Gto the root of Li
	
			 y = L_roots[tree];
			 side = 2;
	}
	if (x == y)														//there is no unlabeled edge in the fundamental cycle
		return -1;	
	
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
					//cout<<x<<" "<<parent[tree][x]<<" "<<Gfrom[q]<<" "<<Gto[q]<<endl;
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
						//cout<<"call with "<<Gfrom[q]<<" "<<Gto[q]<<endl;
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
   int res = Label_A_step(e, i);
   return res; 
}
int Next_edge_step(){
	    int myedge;
		int found_joining;
		int i = 0;
		while(!myQ.empty()){
			myedge = myQ.front();													//extract  the first element(edge) Gfrom the queue
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
	for (int i = 0; i <= current_Tree; i++){
			L_roots[i] = x;
			labelled[i][x] = 1;				
	}
}
void Empty_the_queue(){
	int f;
	while (!myQ.empty()) {								
	
		f = myQ.front();
			labels[f] = -1;
			myQ.pop(); 
	}
}
int search_joining(int x){
	int y;
	int joining_edge;														
    int e;
	augmenting_root = x;															//global variable that shows which vertex is about Gto be increased
	for (int j = GfirstIn[x]; j < GfirstIn[x+1]; j++){								//look on the incoming arcs
	
			e = positionIn[j];
			y = Gfrom[e];
			y = root[y];															//find the root of the f-tree
			if (edge_state[e] == unused){											//if the edge is available			
					if ( x != y){													//and the f-trees have diferrent root
						Empty_the_queue();
						join(e);										            //assign the edge j Gto the current_tree (easy case)
						return 1;
					}
					else{														    //if the f trees have the same root(cycle) 
																					//add the edge in the queue
						 labels[e] = - 2;											//label the edge with (-2) sign that indicates the first edge of the path
						 myQ.push(e);												
					}
			}		
	}
	// if i did not find free joining edge, i go Gto see if i can have one via a sequence of swaps.

	
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
	 turn_subtrees_active(); 
	 order_edges_from_trees();
	for (int j = 0; j <= current_Tree; j++ ){
	    	if (tree_flag[j] == 1 || j == current_Tree || j == 0){	
				update_parents_depths( j );
			}
	}
	 for (int j = 0; j <= current_Tree; j++){
	 
		L_roots[j] = -1;								//clear roots of every L_i
		tree_flag[j]= -1;
		for (int i = 1; i < n+1; i++){  
		
			labelled[j][i] = -1; 						//all nodes Gfrom every Ti are becoming unlabelled
		}
	}		
	for (int i = 0; i < m; i++)   labels[i] = -1;		//clear the label of every edge 
		for (int i = 0; i < K*n; i++)  edges[i] = -1;
	next_f_tree = 1;
}

void Augmentation_Algorithm(){
	int i = 0;
    int e,s;
	while(!joining_edges.empty()){
	
		e = joining_edges.front();													//extract  the first element(edge) Gfrom the queue
		    joining_edges.pop();
			
		s =	joining_edges.front();													//extract  the first element(edge) Gfrom the queue
		    joining_edges.pop();
		trace_back(e, s);
	}
}
void increase_memory_for_new_tree(){
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
		
		while (njoins < n - 1){
			z = choose_root();										//returns the root of an active subtree, or -1, in case of no acive subtree exists.
			while (z != -1){
				if (search_joining( z ) == 1){						//increase the root z of the coresponding f_tree  if it is possible
					njoins++;
					//cout<<njoins<<endl;
				}
				else{												//otherwise halt

					printf("\n There is %d intersection\n", current_Tree);
					return current_Tree;
				}
				z = choose_root();									//continue untill no active f_tree exists
			}
			Augmentation_Algorithm();								//trace out the paths in order Gto transfer the edges Gto the appropriate Ti								
			//printTree(0);
			//cin>>z;
			reInit();												//reinit data structures and make all f_trees active for the next
			
		}
		cout<<"tree "<<j+1 <<" is ok "<<endl;	
	}
	return K;
}
void Define_upper_bound_of_K(){
	int *degrees;
	degrees = new int[ n + 1];
	int min = 0;
	
	degrees[min] = n*n;

	for (int i = 1; i < n + 1 ; i++){
		degrees[i] = GfirstOut[i+1] - GfirstOut[i] + GfirstIn[i+1] - GfirstIn[i];
		if (degrees[i] < degrees[min]){		
			min = i;	
		}
	}
	
	K = degrees[min] + 1;
	//cout<<"min is "<<K<<endl;
	delete [] degrees;
}
void Gabow(Graph *G){	
	GfirstIn = new int [n+2];
	GfirstOut = new int [n+2];
	Gout = new int[m];
	Gin = new int[m];
	positionIn = new int[m];
	positionOut = new int[m];
	positionIn = G->positionIn;
	positionOut = G->positionOut;
	GfirstIn = G->GfirstIn;
	GfirstOut = G->GfirstOut;
	Gout= G->Gout;
	Gin=G->Gin;
    Define_upper_bound_of_K();
	K = construct_trees();	
	G->mybranchings = K;
	G->nextbranching = 0;
	cout<<"K is "<<K<<endl;
	cout<<"End of Gabow"<<endl;
}
//---------END OF GABOW-----------//
/////////////////////////////////////////////////////

/*---------FORD AND FULKERSON-----------*/


// return the origin x of edge (x,y)
inline int Graph::edgeFrom(int k) {
	return from[k];
}

// return the target y of edge (x,y)
inline int Graph::edgeTo(int k) {
	return to[k];
}

// if v is the origin of the edge k, then return its flow
// otherwise, return 1-flow
inline int Graph::edgeFlow(int k, int v) {

   int   x = from[k];
   int y = to[k];
   int f = Flow[k];  // edge flow

	if (v == x) return f;
	if (v == y) return 1 - f;
	exit(-1); // error!
}

inline void Graph::setEdgeFlow(int k, int f) {
	Flow[k] = f;
}

// if v is the origin of the edge k, then return 1-flow
// otherwise, return flow
inline int Graph::edgeCapacity(int k, int v) {
	int x = from[k];  // from node
	int y = to[k];  // to node
	int f = Flow[k];  // edge flow

	if (v == x) return 1-f;
	if (v == y) return f;
	
	cout<<"exit from edge capacity"<<endl;
	exit(-1); // error!
}

// v must be an endpoint of the edge k=(v,w) or k=(w,v). 
// returns w
inline int Graph::edgeOther(int k, int v) {
	
	int x = from[k];  // Gfrom node
	int y = to[k];  // Gto node

	if (v == x) return y;
	if (v == y) return x;
	cout<<"error"<<endl;
	exit(-1); // error!
}

// execute a breadth-first search Gto find a path Gfrom s Gto t 
bool Graph::findPath(int s, int t) {

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
			  int k = Gadj[i]; 		  
			if (usable[k] == 0) {		
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

// add 1 unit Gto the residual flow of edge k 
// if k = (u,v) then flow of k becomes 1
// if k = (v,u) then flow of k becomes 0
inline void Graph::addResidualFlowTo(int k, int v)
{
	if (v == to[k]) setEdgeFlow(k, 1);
	if (v == from[k]) setEdgeFlow(k, 0);
}

inline void Graph::augmentFlow(int s, int t)
{
	int v = t;
	while (v != s)
	{
		int k = pathEdge[v];
		addResidualFlowTo(k, v);
		v = edgeOther(k, v);
	}	
}
// use FordFulkerson method to compute a flow Gfrom s to t of value at most f_max
int Graph::FordFulkerson(int s, int t, int f_max){

	if (s == t) return -1;
	int totalFlow = 0;
	
	
	// reset all flows 
    for (int k=0; k<m; k++) Flow[k]=0;
	
	while ( (findPath(s,t)) && (totalFlow <= f_max) ) {
		augmentFlow(s, t);
		totalFlow++;
	}
	return totalFlow; 
}

//---------END OF FORD AND FULKERSON-----------
///////////////////////////////////////////////////////////////////////////////////

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

void Graph::printGraph(int k){
	
		if (idGraph == 1){cout<<"printing Graph G1"<<endl;}
		else if (idGraph == 2){cout<<"printing Graph G2"<<endl;}
		else if (idGraph == 0){cout<<"printing Graph G"<<endl;}
		
		
	
		
		for (int i = 1; i< n +1 ;i++){	
			//cout<<" real node "<<i<<" correspond to the vertex "<<vertices[i]<<endl;	
	    }
		cout<<endl;
		
		if (idGraph == 1){
			cout<< "T1 {";
			for (int i = 0; i < n; i++){
				if (T[0][i] != -1 ){
					int u =Gfrom[T[0][i]];
					int v = Gto[T[0][i]];
					cout <<u<<" -> "<<v <<" ";
				}
				else{break;}
			}
			cout<< "}\n";
		}
		if (idGraph == 2){
			cout<< "T2 {";
			for (int i = 0; i < n; i++){
				if (T[0][i] != -1 ){
					int u =Gfrom[T[0][i]];
					int v = Gto[T[0][i]];
					cout <<u<<" -> "<<v <<" ";
				}
				else{break;}
			}
			cout<< "}";
		}
		
	 myname++; 
	//ofstream myfile(to_string(myname));
	 //if (myfile.is_open()) {
		//myfi << "p "<<n<<" "<<m<<" "<<r<<endl;
    //}
   // else cout << "Unable to open file";
    cout<<"n is "<<n<<" and m is "<<m<<endl;
	cout<<"\nadjencecy list"<<endl;
	for (int i = 1; i< n + 1;i++){
		cout<<i<<" :";
		for (int j =  Gfirst[i]; j<  Gfirst[i+1];j++){	
			int e=Gadj[j];
			int v = edgeOther(e, i);
				if (v == to[e]){
					cout<<" "<<v;
				}
		}
	    cout<<endl;
	}
   // myfile.close();
    cout<<"------end of printing Graph---------"<<endl;   
}
void Graph::printBranchings(int next){
		
	for (int i = 0; i < K; i++){
		cout <<"branching "<<i<<"  is : "<<endl;
		for (int j = 0; j< n-1 ;j++){
			int e = T[i][j];
			   cout<<Gfrom[e]<<" "<<Gto[e]<<endl;
			    //cout<<e<<endl;
		}
      // cout<<endl;		
	}
}
int Graph::find_edge(int x){
	
	/* This function finds an edge*/
	
	int e, v;	
	int index = x +1;
	int u = S[index];
	while (1){ 
		for (int i = Gfirst[u]; i < Gfirst[u+1]; i++){	
			e = Gadj[i];	
			v = edgeOther( e, u);
			if (vertex_flag[v] == 0 && usable[e] == 0 && to[e] == v){
				//cout<<" select edge "<<u<<" "<<v<<" "<<Gfrom[edgesID[e]]<<" "<<Gto[edgesID[e]]<<endl;
				return e;			
			}								
		}
        if (++index == n + 1) break;		
		u = S[index];		
	}
	return -1;
}

void Graph::merge_branchings(int b1, int b2, int b, int e){
	
	/* This function merge the branching b1 from G1 and b2 from G2 */
	
	int i;
	int e2;
	int reale;
	int c = 0;
	
	for ( i = 0; i < G1->n-1; i++){
		 reale = G1-> T[b1][i];
		if (reale != e){
			T[b][c++] = G1-> T[b1][i];	 
		} 
	}
	for (int j = 0; j < G2->n-1; j++){
		reale = G2-> T[b2][j];
		if (reale != e){
			T[b][c++] = G2-> T[b2][j];	
		}
	}
	assert(c==n-2);
    T[b][c] = e; 
}
void Graph::combine(int splitted_edge){
	
	/* This function combines the branchings of G1 and G2 to obtain the final branchings*/
	
	int *left_edges = new int [global_m];
	int *right_edges = new int [global_m];
	//int *exists = new int [global_m];
	
	int e,e1,e2,k,k2;
	int b1,b2;
	
	bool *left_branchings_paired = new bool[mybranchings];
	bool *right_branchings_paired = new bool[mybranchings];
	
	int Branching = nextbranching;
	int tt;
	
for (int i = 0; i < global_m; i++) {
	//exists[i] = 0;
	left_edges[i]=-1;
	right_edges[i]=-1;
}
	
for (int i = 0; i < mybranchings; i++){
	left_branchings_paired[i] = false;
    right_branchings_paired[i] = false;

	for (int j = 0; j < G1->n-1;j++){	
		e = G1-> T[i][j];
		left_edges[e] = i;      //shmeiwnoume se pio brnching anhkei h kathe akmi;
		//exists[e]++;
	}	
	for (int j = 0; j < G2->n-1;j++){	
		e = G2-> T[i][j];		
		right_edges[e] = i;    //shmeiwnoume se pio branching anhkei h kathe akmi;
		//exists[e] ++;
	}	
}


for (int i = G1->Gfirst[1]; i < G1->Gfirst[2];i++){
	k = G1->Gadj[i];
		e1 = G1->edgesID[k];
		b1 = left_edges[e1];//den einai valid  tob1 !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
		if (left_branchings_paired[b1] == false){
			for (int j = G2->Gfirst[2]; j < G2->Gfirst[3];j++){
				k2 = G2->Gadj[j];
						e2 = G2->edgesID[k2];	
						b2 = right_edges[e2];//den einai valid  to b2 !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
					//	cout<<"e2 is "<<"		"<<e2<<endl;
					if (right_branchings_paired[b2] == false){
						//cout<<"e1= "<<e1<<", e2= "<<e2<<"---"<<b2<<" -------- "<<k2<<"--------"<<e2<<endl; 
							if (e2 == e1 ){
								//cout<<"pairing "<<b1<<" with "<<b2<<endl;
								left_branchings_paired[b1] = true;
								right_branchings_paired[b2] = true;
								merge_branchings(b1,b2, Branching,e1);
								Branching++;
								break;						
							}
					}
			}   	
		}
}
 
	delete [] left_edges;
	delete [] right_edges;
	delete [] left_branchings_paired ; 
	delete [] right_branchings_paired;
   // delete [] exists;	
	//cout<<"---end of combine---"<<endl;
}
void Graph::init_tree(int i, int call){

/* This function initializes the stractures of a branching before computing it*/	
	
  if (call == 1 || idGraph == 0){	
    for (int j = 0; j < n; j++){
        T[i][j] = -1;
		Tedge[j] = -1;
	}		
	for (int j = 1; j <n +1; j++){//set all flags vertices (vertices outside of my set) 
		vertex_flag[j] = 0;
	    S[j] = -1;
	}
	
	for (int x=0;x<m;x++){isT[x]=0;}
	
	//first vertex in the set S
	nextS = n;
	S[nextS--] = r;							
	vertex_flag[r] = 1;
  }
}

/*void Graph::computeS(){
	
	//Compute the vertices of S and V/S
inS = new int[n+2];	
for (int i = 1; i < n + 1; i++){	
	if (marked[i] == true ){	
		inS[i] = 1;	
		//cout<<"in S: "<<i<<endl;
	}
	else{
		inS[i] = -1;
	}
}
}*/

void Graph::split(int e, int i, int j){
	
	/* When splitting must be done*/
		
	//computeS();							     //compute the set S and V-S (vertices of G1, G2)	
	usable[e] = 0;	
	
	G1 = new Graph();						
	idGraph = 1;
	int index1 = passing_paremetersG1(G1);	
	G1-> createGadj(this->from, this->to);
	//G1->printGraph(K);
    G1->find_branchings(index1);
	
	//cout<<"G1 is ok "<<endl;
	//cout<<"----printing branchings of G1-------vertices: "<<G1->n<<endl;
	//G1->printBranchings(K);	
	//cout<<"----End of printing branchings of G1-------vertices: "<<G1->n<<endl;
	
	G2 = new Graph();
	idGraph = 2;
	int index2 = passing_paremetersG2(G2);	
	G2-> createGadj(this->from, this->to);
	//G2->printGraph(K);
    G2->find_branchings(index2);	   	
	//cout<<"--------printing branchings of G2----vertices: "<<G2->n<<endl;
	//G2->printBranchings(K);
	//cout<<"----End of printing branchings of G2-------vertices: "<<G2->n<<endl;
    
}
void Graph::find_branchings(int index){
	
	/*Main routine of the algorithm which find the branchings*/
	
	int Con;
	int u,tt;
	int k = mybranchings;
	int j = index;
	int z  = 0;
     
	 
	// cout<<"my index is "<<j<<endl;
	while(nextbranching != k){		   
	      init_tree(nextbranching, z);
		  z = 1;
		while(nextS != 0){                              //while my set does not include all the nodes	
			int e = find_edge(nextS);					
			if (e == -1){cout<<"error edge not found "<<endl;exit(1);}
			
			usable[e] = 1;
			if (nextbranching < k -1 ){
				Con = FordFulkerson(r, to[e], mybranchings);
			}
			else if (nextbranching == k - 1){		     
				Con = 0;	 				
			}
			
			if (Con >= mybranchings - 1){	
               u = to[e];  
			   S[nextS--] = u;
			   Tedge[j] = e;
			   T[nextbranching][j++] = edgesID[e];
			 //  cout<<"in position"<<nextbranching<<" "<<j-1<<endl;
			   isT[e] = 1;
               vertex_flag[u] = 1;// u is inserted in T
			}
			else{
				n_splits++;
				//cout<<"SPLIT "<< n_splits<<endl;
				// Tedge[j] = e;
				// isT[e] = 1;
			     split(e, nextbranching, j);
                				 
				 combine(e);
				 return;
			}
		} 
		mybranchings--;
		nextbranching++;
		j = 0;
		//cout<<"branching "<<nextbranching<< " is ready"<<endl;	
	}
}
void Graph::BuildGraph() {

	/* Building adjacency lists of the graph for the execution of Gabow initially. */

    int x,y,e;
    int *GnextOut = new int [n+2];
    int *GnextIn  = new int [n+2];
	Gout = new int [m];
    GfirstOut = new int [n+2];
	positionOut = new int[m];	
	
    Gin  = new int [m];
    GfirstIn  = new int [n+2];	
    positionIn = new int[m];
	Gfrom = new int[m];
    Gto = new int[m];
	
	
    for (int i=0; i < this-> m; i++){
		Gin[i] = Gout[i] = 0;
		positionIn[i] = -1;
		positionOut[i] = -1;    
		Gfrom[i] = -1;
		Gto[i] = -1;
	}
    for (int i=0; i<=n+1; i++){
		GfirstOut[i] = GnextOut[i] = GfirstIn[i] = GnextIn[i] = 0;
	}

    for (int k=0; k < this->m; k++)
    {
		x = input_file[2*k];
		y = input_file[2*k+1];
		Gfrom[k] = x;
		Gto[k] = y;		
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
		
        Gout[GnextOut[x]++] = y;
        Gin[GnextIn[y]++] = x;			 
    } 
    delete [] GnextIn;
    delete [] GnextOut;
}
int Graph::passing_paremetersG1(Graph *nextGraph){
	
	/* parameters of Graph G1 after split*/
	
 int n_vertices = 2;
 int n_edges =0;
 int x;
 int y;
 int edge_id;
 int *myedges = new int[2*m];
 int *myvertices = new int[n+1];
 int *myedges_id = new int[2*m];
 int *previous_usable = new int [m];
 
	
for (int i = 1; i < n+1; i++){  //diorthwsi me komvous
	if (marked[i] ==  false){	  
		myvertices[i] =  n_vertices++;	
	}	
	else{
		myvertices[i] = 1;
	}		  
}
for (int i = 0; i < m; i++){	
	previous_usable[i] = -1;	
}
for (int i = 1; i < n+1; i++){   //count edges of the new graph
	for (int j = Gfirst[i]; j < Gfirst[i+1]; j++){
		int k = Gadj[j];
		edge_id = edgesID[k];
		y = to[k];
        // cout<<"test  "<<i<<" "<<y<<endl;			
		if (marked[y] == false && usable[k] == 0 && y != i){
			myedges[n_edges] = k;
            myedges_id[n_edges++] = edge_id;
           // cout<<"1 is inserted "<<from[k]<<" "<<to[k]<<endl;			
		}
		if (isT[k] == 1 && marked[y] == false && y!=i){
			myedges[n_edges] = k;
			previous_usable[k] = n_edges;
            myedges_id[n_edges++] = edge_id;
           // cout<<"2 is inserted  "<<from[k]<<" "<<to[k]<<endl;			
		}
	}		
}
int c;
int index = 0;

   nextGraph->n = n_vertices-1;
   nextGraph->m = n_edges;
   nextGraph->r = r;	
   c = nextGraph->n;
   nextGraph->mybranchings = mybranchings;	
   nextGraph->nextbranching = 0; 
   nextGraph->Tedge = new int[nextGraph->n+1];
   nextGraph->vertex_flag = new int[nextGraph->n +1];
   nextGraph->S = new int[nextGraph->n + 1];
   nextGraph->isT = new int[nextGraph->m];
 
   nextGraph->T = new int* [mybranchings];
   for (int i = 0; i < mybranchings; i++){
	 nextGraph->T[i] = new int[nextGraph->n];		  
   }
    nextGraph->usable = new int[n_edges];
	for (int i= 0; i < n_edges; i++){
		nextGraph->usable[i] = 0;
		nextGraph->isT[i] = -1;
		
	}
	for (int i=0; i < m; i++){
		int k = previous_usable[i];
		if ( k != -1){
			nextGraph->usable[k] = 1;
			nextGraph->isT[k] = 1;
		}
	}	
   
   
  for (int i = 0; i < nextGraph->n + 1; i++){
	 nextGraph->vertex_flag[i] = 0;		  
	 nextGraph->S[i] = -1;		  
	 nextGraph->Tedge[i] = -1;
      if (i < nextGraph->n) nextGraph->T[0][i] = -1;		 
   }	   
	nextGraph->vertex_flag[r]=1;
	nextGraph->S[c--] = r;
    for (int j = 0; j < n; j++){
		int e = Tedge[j];
		if (e != -1){
			x = from[e];
			y = to[e];
			if (marked[y] == false){
				nextGraph->Tedge[index] = previous_usable[e];
				nextGraph ->T[0][index++] = edgesID[e];	
				x = myvertices[x];
				y = myvertices[y];
				if (nextGraph->vertex_flag[x] != 1){
					nextGraph->vertex_flag[x] = 1;
					nextGraph->S[c--] = x; 
				}
				if (nextGraph->vertex_flag[y] != 1){
					nextGraph->vertex_flag[y] = 1;
					nextGraph->S[c--] = y;
				}
			}
        }		
	}
nextGraph->nextS = c;  	
nextGraph->edges = new int[n_edges];
nextGraph->edgesID = new int[n_edges];
nextGraph->vertices = new int[n+1];
nextGraph->level = level + 1;
		
for (int j =0; j < n_edges; j++ ){
	nextGraph->edges[j] = myedges[j];
    nextGraph->edgesID[j] = myedges_id[j];				
}	
for (int j = 1; j < n+1; j++){
	nextGraph->vertices[j] = myvertices[j];
} 

delete []myedges;
delete []myvertices;
delete []myedges_id;
delete [] previous_usable;

return index;


}
int Graph::passing_paremetersG2(Graph *nextGraph){
	
	
	/* parameters of Graph G2 after split*/	
 int n_vertices = 3;
 int n_edges =0;
 int x;
 int y;
 int edge_id;
 int edge;
 int *myedges = new int[2*m];//pairnei to m kai n tou prohgoumenou grafimatos G
 int *myvertices = new int[n+1];
 int *myedges_id = new int[2*m]; 
 int count_edges_to_T = 0;
 int *edges_to_T = new int[m];
 int *parent = new int[n+1];
 int index = 0;
 int *inT = new int[m];
 int *previous_usable = new int [m];
 

 
 for (int i = 1; i < n +1; i++){  
	if (i == r){		
		myvertices[r] = r; //h riza exei to id ths rizas
	 }
	 else  if (marked[i] == true){	  
		 myvertices[i] =  n_vertices++;	  //count vertices of the new graph each vertex is mapped to the ew id for the new graph
	 }	
     else{
		myvertices[i] = 2;// o yperkomvos exei id 2
	}	  
 }
 for (int i = 0; i < m; i++){
	inT[i] = -1 ;	
	previous_usable[i] = -1;	
 }
 
for (int i = 1; i < n + 1; i++){   //count edges of the new graph G2
	for (int j = Gfirst[i]; j < Gfirst[i+1]; j++){
		int k = Gadj[j];
		edge_id = edgesID[k];
		y = to[k];
		
		if ( isT[k] == 1 && marked[y] == false && marked[i] == true && y!=i){
				edges_to_T[count_edges_to_T++] = k;            //edw prosthetoume akmes apo to S sto V - S poy einai sto T
				inT[k] = 1;				
		}
		if (marked[y] == true && isT[k] == 1 && inT[k] != 1 && y!=i){
			myedges[n_edges] = k;
			previous_usable[k] = n_edges;
            myedges_id[n_edges++] = edge_id;
           // cout<<"is inserted 1 "<<from[k]<<" "<<to[k]<<endl;			
		}
		if (usable[k] == 0 && marked[i] == true && y != i){
				myedges[n_edges] = k;
                myedges_id[n_edges++] = edge_id;
                 // cout<<"is inserted 2 "<<from[k]<<" "<<to[k]<<endl;					
		}
		else if (usable[k] == 0 && marked[i] == false && y!=i){
			if (marked[y] == true){
				myedges[n_edges] = k;
                myedges_id[n_edges++] = edge_id;
                 // cout<<"is inserted 3 "<<from[k]<<" "<<to[k]<<endl;					
			}
		}			
	}					
}
 for (int i = 0; i < n + 1; i++) parent[i] = -1;
 
 for (int i = 0; i < n+1; i++){   // edw ftiaxnoume ton pinaka parent
	  int e = Tedge[i];
	  if ( e != -1 ){	  
		x = from[e];
		y = to[e];
        parent[y] = x;			
	  }
}	  
 
int flag = 0;
	
	for (int i = 0; i < count_edges_to_T ; i++ ){  //edw prospathoume na broume mia akmh apoo pros to t gia to G2
		int e = edges_to_T[i];
		     x = from[e];
		while (x != -1 && x!=r){			
            if (marked[x] == false) break;
            x = parent[x];
           // cout<<x<<endl;			
		}
		if (x == r){
			//cout<<x<<endl;
			flag = 1;
			inT[e] = 0;
			myedges[n_edges] = e;
	        previous_usable[e] = n_edges;
            myedges_id[n_edges++] = edgesID[e];
			break;			 
		}
	}	
//}
if (flag == 0) {
	cout<<"error in line 1574--"<<endl;
	exit(-1);
}
else if (flag ==1) {
	//cout<<"found--"<<endl;
	//int tt; cin>>tt;
	
}
int c;
nextGraph->n = n_vertices-1;
nextGraph->m = n_edges;
nextGraph->r = r;	
c = nextGraph->n;

nextGraph->mybranchings = mybranchings;	
nextGraph->nextbranching = 0;
nextGraph-> Tedge = new int[nextGraph->n+1];
nextGraph->vertex_flag = new int[nextGraph->n +1];
nextGraph->S = new int[nextGraph->n + 1];
nextGraph->isT = new int[nextGraph->m];

nextGraph->T = new int* [mybranchings];
for (int i = 0; i < mybranchings; i++){
	nextGraph->T[i] = new int[nextGraph->n];		  
}	
nextGraph->usable = new int[n_edges];
for (int i= 0; i < n_edges; i++){
	nextGraph->usable[i] = 0;
	nextGraph->isT[i] = -1;
	
}
for (int i = 0; i < m; i++){
	int k = previous_usable[i];
	if ( k != -1){
		nextGraph->usable[k] = 1;
		nextGraph->isT[k] = 1;
	}
}
for (int i = 0; i < nextGraph->n + 1; i++){
	nextGraph->vertex_flag[i] = 0;		  
	nextGraph->S[i] = -1;		  
	nextGraph->Tedge[i] = -1;	
    if (i < nextGraph->n) nextGraph->T[0][i] = -1;	
}	
nextGraph->vertex_flag[r]=1;
nextGraph->S[c--] = r;
for (int j = 0; j < n; j++){
	int e = Tedge[j];
	if (e != -1 && inT[e] != 1){
		x = from[e];
		y = to[e];
		if (marked[x] == true || marked[y] == true){
			nextGraph->Tedge[index] = previous_usable[e];			
			nextGraph ->T[0][index++] = edgesID[e];		
			x = myvertices[x];
			y = myvertices[y];
			if (nextGraph->vertex_flag[x] != 1){
				nextGraph->vertex_flag[x] = 1;
				nextGraph->S[c--] = x; 
			}
			if (nextGraph->vertex_flag[y] != 1){
				nextGraph->vertex_flag[y] = 1;
				nextGraph->S[c--] = y;
			}
		}
    }		
}

nextGraph->nextS = c;  				
nextGraph->edges = new int[n_edges];
nextGraph->edgesID = new int[n_edges];
nextGraph->vertices = new int[n+1];	
nextGraph->level = level + 1;

for (int i =0; i < n_edges; i++ ){
	nextGraph->edges[i] = myedges[i];
    nextGraph->edgesID[i] = myedges_id[i];						
}	
for (int i = 1; i < n+1; i++){
	nextGraph->vertices[i] = myvertices[i];
}
	
delete []myedges;
delete []myvertices;
delete []myedges_id;
delete [] edges_to_T;
delete [] parent;
delete [] inT;
delete [] previous_usable;

return index;

}

void Graph::createGadj(int *G1from, int *G1to){	

/* build the adjancecy lists of the graph*/

	int x, y, e;

    if (idGraph == 0){	
		vertices = new int[n+2];
		edges = new int[m];
		edgesID = new int[m];
		level = 0;
		Tedge = new int[n+1];
        vertex_flag = new int[n +1];
	    S = new int[n + 1];
		isT = new int[m];
        T = new int* [mybranchings];
	    for (int i = 0; i <mybranchings; i++){
		    T[i] = new int[n];		  
	    }
        usable = new int [m];
		for (int i=0; i < m; i++){
			usable[i] = 0;
		}		
	}
	pathEdge = new int[n+1]; 
	marked = new bool[n+1];	
	Flow = new int[m];
	from = new int[m];
	to = new int[m];
	

	Gadj = new int[2*m];
	Gfirst = new int[n + 2];

	int* Gnext = new int[n + 2];
	
	
     for (int i = 0; i < 2 * m; i++){
		 Gadj[i] = -1;
	 }		
	for (int i=0; i<=n+1; i++){ 
		Gfirst[i] = 0; 
		if (idGraph == 0) vertices[i] = i;
	}
    for (int k=0; k<m; k++)
    {
		if (idGraph == 0){
			x = input_file[2*k];
			y = input_file[2*k+1];
			edges[k] = k;
			edgesID[k] = k;
		}
		else{	
			e = edges[k];				//e einai h akmh tou proigoumenou grafimatos
			x = G1from[e];				//to x einai o enarktirios komvos ths e 
			y = G1to[e];
			x = vertices[x];
			y = vertices[y];
		}	
		from[k] = x;
		to[k] = y;
		
		if (x!=y){
			Gfirst[x + 1]++;
		    Gfirst[y + 1]++;
		}
		else{
			Gfirst[x + 1]++;
		}
    }
	for (int k = 1; k <= n+1; k++) {	
		Gfirst[k] += Gfirst[k - 1];
		Gnext[k] = Gfirst[k];
    }
    for (int k = 0; k < m; k++)
    {
		if (idGraph == 0){
			x = input_file[2*k];
			y = input_file[2*k+1];
			e = k;
		}
		else{
			e = edges[k];
			x = G1from[e];	
		    y = G1to[e];
			x = vertices[x];
			y = vertices[y];
           
           // if (usable[k] == 1)	cout<<"usable in create "<<from[k]<<" "<<to[k]<<endl;	   
		}
		if (x!=y){
			Gadj[Gnext[x]++] = k;
			Gadj[Gnext[y]++] = k;
		}
		else{	
			Gadj[Gnext[x]++] = k;		
		}
	}	
	delete [] Gnext;
}
void Graph::GgetValues(int x, int y, int z){	
	n  = x;
	m = y;
	r   = z;
    global_m = y;
    global_n = x;	
}

int main(int argc, char *argv[]){


	 if (argc != 2) {
        printf("\n usage: %s <input file> \n\n", argv[0]);
        exit(-1);
     }

	 char* file = argv[1];
	 
	 readGraph(file);	//reading graph Gfrom file
	 
	 Graph G;
	 idGraph = 0;
	 G.GgetValues(n, m, r);
	 G.BuildGraph();
     Gabow(&G); 
	 G.createGadj(NULL,NULL);
	
	
	using namespace std::chrono;
	high_resolution_clock::time_point t1 = high_resolution_clock::now();
	
	 G.find_branchings(0);
	 
	high_resolution_clock::time_point t2 = high_resolution_clock::now();
	duration<double> time_span = duration_cast<duration<double>>(t2 - t1);
	std::cout << "Running time " << time_span.count() << " seconds.";
	std::cout << std::endl;
	cout<<"Number of splits: "<<n_splits<<endl; 
	  
    return 0;
}