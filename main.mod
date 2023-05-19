main {	
	var data = new IloOplDataSource("test-replace.dat");
 	var source = new IloOplModelSource("test-replace.mod");
 	var def = new IloOplModelDefinition(source);
	for(var day = 1; day < 10; day++) {
	 	for(var i = 1; i < 101; ++i) {
		  	var cplex = new IloCplex();
			var opl = new IloOplModel(def,cplex);
	
		  	var data2 = new IloOplDataElements();
		  	data2.CurrentIteration = (day-1)*100+i;
		  	opl.addDataSource(data2);
		  	opl.addDataSource(data);
		  	
		 	opl.generate();
		 	cplex.solve();
		 	opl.postProcess(); 
		} 
	} 	
	cplex.end();
}