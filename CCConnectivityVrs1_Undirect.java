package CCconnectivity;


import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import ilog.concert.IloException;
import ilog.concert.IloLinearNumExpr;
import ilog.concert.IloNumVar;
import ilog.cplex.IloCplex;

public class CCConnectivityVrs1_Undirect {
	int K=8; //number of the cluster
	int n; //number of the vertices
	int matrixAdj[][]; //graph
	//variables
	public IloNumVar[][] x;
	public IloNumVar[][] y;
	public IloNumVar[][][][] f;
	IloCplex cplex;
	
	public void upload_graph(String path1) {
		FileReader arquivo;
		BufferedReader reader;
		try {
			arquivo = new FileReader(path1);
			reader = new BufferedReader(arquivo);
			try {
				String[] aux = reader.readLine().split(" ");
				n = Integer.valueOf(aux[1]); //number of the vertices
				String line;
				matrixAdj = new int[n][n];
				 while ((line =  reader.readLine()) != null ) {
		                
		                if (line.contains(")") && line.contains(")") && line.contains(",")) {
		                   aux = line.split("\\)");  
		                   if(aux[1].contains("]")) {
		                   String[] auxnew = aux[1].split("\\]");
		                   aux[1] = auxnew[0];
		                   }
		                   
		                   String[] aux2 = aux[0].split(",");
		                   String[] aux3 = aux2[0].split("\\(");
		                   
		                   int u = Integer.valueOf(aux3[1].trim());
		                   int v = Integer.valueOf(aux2[1].trim());
		                   int weight = Integer.valueOf(aux[1].trim());
		                   matrixAdj[u-1][v-1] = weight;
		                   matrixAdj[v-1][u-1] = weight;
		                  
		                }
		         }
				 
				 System.out.println( "N:" + n);
				 for(int i =0; i<n; i++) {
					 for(int j =0; j<n; j++) {
						 System.out.print( " " +  matrixAdj[i][j]);
					 }
					 System.out.println();
				 }
					 
				 
				reader.close();
				arquivo.close();		
				
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	
	public void model() throws IloException {
		cplex = new IloCplex();
		this.x = new IloNumVar[n][K];
		this.y = new IloNumVar[n][n];
		this.f = new IloNumVar[n][n][n][n];

		//created variables x
		for (int i = 0; i < n; i++) {
			for(int k = 0; k <K; k++) {
				x[i][k] = cplex.numVar(0,1, "x(" + i + "," + k + ")");
			}
		}
		
		
		//created variables y
		for (int p = 1; p < n; p++) {
			for (int q = 0; q < p; q++) {
				y[p][q] = cplex.numVar(0,1,"y(" + p + "," + q + ")");
			}
		}
		
		

		//created variables f
		for (int p = 1; p < n; p++) {
			for (int q = 0; q < p; q++) {
				for (int i = 0; i < n; i++) {
					for (int j = 0; j < n; j++) {
						if(matrixAdj[i][j] != 0 && i!= j)
							f[p][q][i][j] = cplex.numVar(0, n,"f(" + p + "," + q + "," + i + "," + j + ")");	
					}
				}
			}
		}
		
		
		
		//Constraints 1: ensures that each vertex belongs to exactly one subgraph
		for(int i=0; i<n; i++) {
			IloLinearNumExpr constraints1 = cplex.linearNumExpr();
			for(int k=0; k<K; k++) {
				constraints1.addTerm(1, x[i][k]);	
			}
			cplex.addEq(constraints1, 1);//
		}
		
		
		
		
		//Constraints 2: states that at most K subgraphs will be created following an ordering
		
		for(int k=0; k<K; k++) {	
			for(int kline=k +1; kline<K; kline++) {
				IloLinearNumExpr constraints2 = cplex.linearNumExpr();
				for(int i=0; i<n; i++) {
					constraints2.addTerm(1, x[i][kline]);
				}
				for(int i=0; i<n; i++) {
					constraints2.addTerm(-n, x[i][k]);
				}
				cplex.addLe(constraints2, 0);//
			}
		}
	
		
		//Constraints 3: The constraints 3 ensures that the variable y_pq will have the value equal
		//to one if the vertices p and q are in the same subgraph
		
		for(int k=0; k<K; k++) {	
			for(int p=1; p<n; p++) {
				for(int q=0; q<p; q++) {
						IloLinearNumExpr constraints3 = cplex.linearNumExpr();
						constraints3.addTerm(1, x[p][k]);
						constraints3.addTerm(1, x[q][k]);
						constraints3.addTerm(-1, y[p][q]);
						cplex.addLe(constraints3, 1);
						
						IloLinearNumExpr constraints4 = cplex.linearNumExpr();
						constraints4.addTerm(1, x[p][k]);
						constraints4.addTerm(-1, x[q][k]);
						constraints4.addTerm(1, y[p][q]);
						cplex.addLe(constraints4, 1);
						
						IloLinearNumExpr constraints5 = cplex.linearNumExpr();
						constraints5.addTerm(-1, x[p][k]);
						constraints5.addTerm(1, x[q][k]);
						constraints5.addTerm(1, y[p][q]);
						cplex.addLe(constraints5, 1);
				}
			}
		}
		
		
		
		//Constraints 6 e 7: ensures that the flow sent from $p$ to $q$ must contain value two, 
		//how each flow variable has the maximum capacity
		//with value equal to one, two disjoint paths will be constructed for each pair $p, q \in V$
		for (int j = 0; j < n; j++) {
			for(int p=1; p<n; p++) {
				for(int q=0; q<p; q++) {		

				if( p!= q && matrixAdj[p][q]!=0 ) {	
					IloLinearNumExpr constraints4 = cplex.linearNumExpr();
					
					
					for (int i = 0; i < n; i++) {
						if (matrixAdj[i][j] != 0 && i!= j) {
							constraints4.addTerm(1, f[p][q][i][j]);
						}
						if (matrixAdj[j][i] != 0 && i!= j) {
							constraints4.addTerm(-1, f[p][q][j][i]);
						}
					}
						
					if (j == p) {
						cplex.addEq(constraints4, cplex.prod(-2, y[p][q]));//
					} else if (j == q)  {
						cplex.addEq(constraints4, cplex.prod(2, y[p][q]));
					} else {
						cplex.addEq(constraints4, 0);
					}	
				}

				}
			}
		}
		
		//Constraints 5
		// Warning: since the edge variables are created for an undirected graph, y_i_j does not always exist
		for(int i=0; i<n; i++) {
			for(int j=0; j<n; j++) {
				for(int p=1; p<n; p++) {
					for(int q=0; q<p; q++) {	
						if(matrixAdj[i][j]!=0  && i!= j) {	
							IloLinearNumExpr constraints5 = cplex.linearNumExpr();
							constraints5.addTerm(1, f[p][q][i][j]);
							
							if(i>j)
								constraints5.addTerm(-1, y[i][j]);
							else if(j>i)
								constraints5.addTerm(-1, y[j][i]);
							
							cplex.addLe(constraints5, 0);
						}
					}
				}
			}
		}
	
				
		//objective function
				IloLinearNumExpr objective = cplex.linearNumExpr();
				double sum =0;	
					for(int p=1; p<n; p++) {
						for(int q=0; q<p; q++) {
							if (matrixAdj[p][q] < 0)
								objective.addTerm(Math.abs(matrixAdj[p][q]), y[p][q]);
						}
					}
				
					
					for(int p=1; p<n; p++) {
						for(int q=0; q<p; q++) {
							if (matrixAdj[p][q] > 0) {
								sum += Math.abs(matrixAdj[p][q]);
								objective.addTerm(-1*Math.abs(matrixAdj[p][q]), y[p][q]);
							}	
						}
					}
				
				cplex.addMinimize(cplex.sum(objective, cplex.constant(sum)));
			
				
				//int strategy = 3;
				//cplex.setParam(IloCplex.BooleanParam.Benders.Strategy, strategy);
				
				
				
		//created model .lp		
		cplex.exportModel("model.lp");
				
		//solver the problem
				
		double duration = 0;
		double[][] valueOfX = new double[n][K];
		double[][] valueOfY = new double[n][n];
		double[][][][] valueOfF = new double[n][n][n][n];
		
		double startTime = System.currentTimeMillis();
				
				if (cplex.solve()) {
					double currentTime = System.currentTimeMillis();
					duration = (currentTime - startTime)/1000;
					//update values of the variables
					for(int i=0; i<n; i++) {	
						for(int k=0; k<K; k++) {
								valueOfX[i][k] = cplex.getValue(this.x[i][k]);
						}
					}
					
					for(int p=1; p<n; p++) {
						for(int q=0; q<p; q++) {
							if(matrixAdj[p][q]!=0){
								valueOfY[p][q] = cplex.getValue(this.y[p][q]);
							}
						}
					}
					
					for(int p=1; p<n; p++) {
						for(int q=0; q<p; q++) {
							if(p!=q && matrixAdj[p][q]!=0){
								for(int i=0; i<n; i++) {
									for(int j=0; j<n; j++) {
										if(i!=j && matrixAdj[i][j] != 0){
											if( !((i==p && j==q) || (i==q && j==p)) ){ // exclude the arc (p,q) and (q,p) as the possibility of flow arcs
												valueOfF[p][q][i][j] = cplex.getValue(this.f[p][q][i][j]);
											}
										}
									}
								}
							}
						}
					}
				
				
			}else {
					System.out.println("error - solve");
				}	
				
				
				//print the solution
				for (int i = 0; i < n; i++) {
					for(int k=0; k<K; k++) {
							if(valueOfX[i][k]>0)
							System.out.println("x [" + i + "," + k  +"]= " + valueOfX[i][k]);
					}
				}
					
				
				for(int p=1; p<n; p++){
					for(int q=0; q<p; q++) {
						if(valueOfY[p][q] > 0) {
							System.out.println("y [" + p  + "," + q+ "]= " + valueOfY[p][q]);
						}
					}
				}
				
				
				/*for(int p=1; p<n; p++) {
					for(int q=0; q<p; q++) {
						if(p!=q && matrixAdj[p][q]!=0){
							for(int i=0; i<n; i++) {
								for(int j=0; j<n; j++) {
									if( !((i==p && j==q) || (i==q && j==p)) ){ // exclude the arc (p,q) and (q,p) as the possibility of flow arcs
										if(matrixAdj[i][j] != 0 && i!= j && valueOfF[p][q][i][j]>0){
											System.out.println("f [" + p  + "," + q+ "," + i+ "," + j+ "]= " + valueOfF[p][q][i][j]);
										}
									}
								}
							}
						}
					}
				}*/
				
				//value of the objective function		
				System.out.println("value OF:"+ cplex.getObjValue());
				System.out.println("value Number of the nodes:"+ cplex.getNnodes());
				System.out.println("iterations dual:"+ cplex.getNiterations());
				System.out.println("Tempo de execução:" + duration);
				cplex.end();
				
				
	}
			
		public static void main(String[] args) {
			CCConnectivityVrs1_Undirect m = new  CCConnectivityVrs1_Undirect();
			m.upload_graph("new_instances/haddate.txt");
			try {
				m.model();
			} catch (IloException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		
		
		
	

}
