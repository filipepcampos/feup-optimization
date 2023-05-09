/*********************************************
 * OPL 22.1.1.0 Model
 * Author: filipe
 * Creation Date: 9 May 2023 at 17:37:09
 *********************************************/
 
main
{
  cplex.importModel("allocation.lp");
  writeln(cplex.getObjValue());
}