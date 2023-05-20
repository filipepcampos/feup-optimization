main {	
	var data = new IloOplDataSource("test-replace.dat");
 	var source = new IloOplModelSource("test-replace.mod");
 	var def = new IloOplModelDefinition(source);
	for(var day = 7; day < 10; day++) {
	 	for(var i = 0; i < 31; ++i) {
		  	var cplex = new IloCplex();
			var opl = new IloOplModel(def,cplex);
	
		  	var data2 = new IloOplDataElements();
		  	data2.CurrentIteration = (day-1)*30+i;
		  	opl.addDataSource(data2);
		  	opl.addDataSource(data);
		  	
		 	opl.generate();
		 	cplex.solve();
		 	opl.postProcess(); 
		 	cplex.end();
		} 
	}
}