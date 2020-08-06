/*********************************************
 * OPL 12.6.3.0 Model
 * Author: Mamunur Rahman
 * Creation Date: Jul 31, 2017 at 2:08:10 PM
 *********************************************/
//parameters
int e_value=30000;

// define set
{string} Harvester = ...;
{string} HubStorage = ...;
{string} PreprocessionPlant = ...;
{string} RefineryPlant = ...;
{string} mode = ...;

 float c[mode]=...; 	//cost per unit load per mile
 //float o[mode]=...; 	//cost per order for different modes
 float e[mode]=...; 	//emission of different modes per mile  
 //this should be emission amount per mile per ton, in that case 2nd obj expression need to be modified
 
 float capacity_1[Harvester]=...;		//capacity or demand of facilities
 float capacity_2[HubStorage]=...;
 float capacity_3[PreprocessionPlant]=...;
 float demand_4[RefineryPlant]=...;
 
 /////distance data using tuple////////
 
 //distance d1
 tuple distance_ijm
 {
  string Harvester;
  string HubStorage;
  string mode;
  float distance;  
 }
  {distance_ijm} distance_data_1=...;
 
 float d1[Harvester][HubStorage][mode];
 
 execute {  
 for(var x in distance_data_1) d1[x.Harvester][x.HubStorage][x.mode]=x.distance;
 } 

//distance d2
tuple distance_ikm
 {
  string Harvester;
  string PreprocessionPlant;
  string mode;
  float distance;  
 }
 
 {distance_ikm} distance_data_2=...;

 float d2[Harvester][PreprocessionPlant][mode];

 execute {  
 for(var x in distance_data_2) d2[x.Harvester][x.PreprocessionPlant][x.mode]=x.distance;
 }
 
 
 //distance d3
 tuple distance_jkm
 {
  string HubStorage;
  string PreprocessionPlant;
  string mode;
  float distance;  
 }
 
 {distance_jkm} distance_data_3=...;

 float d3[HubStorage][PreprocessionPlant][mode];

 execute {  
 for(var x in distance_data_3) d3[x.HubStorage][x.PreprocessionPlant][x.mode]=x.distance;
 }
 
 //distance d4
 tuple distance_klm
 {
  string PreprocessionPlant;
  string RefineryPlant;
  string mode;
  float distance;  
 }
 
 {distance_klm} distance_data_4=...;

 float d4[PreprocessionPlant][RefineryPlant][mode];

 execute {  
 for(var x in distance_data_4) d4[x.PreprocessionPlant][x.RefineryPlant][x.mode]=x.distance;
 }
 
 
  //// decision variales
 
 dvar int+ x1[Harvester][HubStorage][mode];
 dvar int+ x2[Harvester][PreprocessionPlant][mode];
 dvar int+ x3[HubStorage][PreprocessionPlant][mode];
 dvar int+ x4[PreprocessionPlant][RefineryPlant][mode];
 
 dvar boolean z1[Harvester][HubStorage][mode];
 dvar boolean z2[Harvester][PreprocessionPlant][mode];
 dvar boolean z3[HubStorage][PreprocessionPlant][mode];
 dvar boolean z4[PreprocessionPlant][RefineryPlant][mode];
 
 
 
  ////objective_1
 dexpr float cost=    sum (i in Harvester, j in HubStorage, m in mode) x1[i][j][m]*d1[i][j][m]*c[m]
 					+ sum (i in Harvester, k in PreprocessionPlant, m in mode) x2[i][k][m]*d2[i][k][m]*c[m]
 					+ sum (j in HubStorage, k in PreprocessionPlant, m in mode) x3[j][k][m]*d3[j][k][m]*c[m]
 					+ sum (k in PreprocessionPlant, l in RefineryPlant, m in mode) x4[k][l][m]*d4[k][l][m]*c[m];
 					
  //objective_2
dexpr float emission= sum (i in Harvester, j in HubStorage, m in mode) z1[i][j][m]*d1[i][j][m]*e[m]
					+ sum (i in Harvester, k in PreprocessionPlant, m in mode) z2[i][k][m]*d2[i][k][m]*e[m]
				    + sum (j in HubStorage, k in PreprocessionPlant, m in mode) z3[j][k][m]*d3[j][k][m]*e[m]
					+ sum (k in PreprocessionPlant, l in RefineryPlant, m in mode) z4[k][l][m]*d4[k][l][m]*e[m];
 					
 minimize cost;
 
 
 subject to{
  
  //Capacity constraints
  Cons_1:
 forall(i in Harvester)
 sum (j in HubStorage, m in mode) x1[i][j][m] + sum (k in PreprocessionPlant, m in mode) x2[i][k][m] <=capacity_1[i];
 
 Cons_2:
 forall(j in HubStorage)
 sum (i in Harvester, m in mode) x1[i][j][m]<=capacity_2[j];
 
 Cons_3:
 forall(k in PreprocessionPlant)
 sum (i in Harvester, m in mode) x2[i][k][m] + sum (j in HubStorage, m in mode) x3[j][k][m] <=capacity_3[k];
 
 //Demand constraints
 Cons_4:
 forall (l in RefineryPlant)
   sum (k in PreprocessionPlant, m in mode) x4[k][l][m] == demand_4[l];
   
   // incoming flow = outgoing flow
   Cons_5:
 forall(j in HubStorage)
 sum (i in Harvester, m in mode) x1[i][j][m] == sum (k in PreprocessionPlant, m in mode) x3[j][k][m];
 
 Cons_6:
 forall(k in PreprocessionPlant)
 sum (i in Harvester, m in mode) x2[i][k][m] + sum (j in HubStorage, m in mode) x3[j][k][m] == sum (l in RefineryPlant, m in mode) x4[k][l][m];
 
 Cons_7:
 forall(i in Harvester, j in HubStorage, m in mode)		///check this constraint if error
 x1[i][j][m] == 0 => z1[i][j][m] == 0;
forall(i in Harvester, j in HubStorage, m in mode)
 x1[i][j][m] >= 1 => z1[i][j][m] == 1;
 
 Cons_8:
 forall(i in Harvester, k in PreprocessionPlant, m in mode)
 x2[i][k][m] == 0 => z2[i][k][m] == 0;
forall(i in Harvester, k in PreprocessionPlant, m in mode)
 x2[i][k][m] >= 1 => z2[i][k][m] == 1;
 
 Cons_9:
 forall(j in HubStorage, k in PreprocessionPlant, m in mode)
 x3[j][k][m] == 0 => z3[j][k][m] == 0;
 forall(j in HubStorage, k in PreprocessionPlant, m in mode)
 x3[j][k][m] >= 1 => z3[j][k][m] == 1;
 
 Cons_10:
 forall(k in PreprocessionPlant,l in RefineryPlant, m in mode)
 x4[k][l][m] == 0 => z4[k][l][m] == 0;
 forall(k in PreprocessionPlant,l in RefineryPlant, m in mode)
 x4[k][l][m] >= 1 => z4[k][l][m] == 1;
 
 //e- constraint method
 cons_11:
 emission <=e_value;
 
   
 }	/// end of model				
 
 
 /// since the decision variables are 3D arrays, to write the results of decision variables in excel file, following tuples are created 
 
 //for decision var x1
 tuple result1			
 {
  string Harvester;
  string HubStorage;
  string mode;
  float amount;
}

{result1} var_x1 = {<i, j, m, x1[i][j][m]> | i in Harvester, j in HubStorage, m in mode };

  //for decision var x2
  tuple result2			
 {
  string Harvester;
  string PreprocessionPlant;
  string mode; 
  float amount;
}

{result2} var_x2 = {<i, k, m,x2[i][k][m]> | i in Harvester,  k in PreprocessionPlant, m in mode };

 //for decision var x3
  tuple result3		
 {
  string HubStorage;
  string PreprocessionPlant;
  string mode;
  float amount;
}

{result3} var_x3 = {<j, k, m, x3[j][k][m]> | j in HubStorage,  k in PreprocessionPlant, m in mode };
 
 // for decision var x4
 tuple result4		
 {
  string PreprocessionPlant;
  string RefineryPlant;
  string mode;
  float amount;  
 }
 
{result4} var_x4 = {<k, l, m, x4[k][l][m]> | k in PreprocessionPlant, l in RefineryPlant, m in mode };

 