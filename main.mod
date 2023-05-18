main {	
	for(var i = 1; i < 3; ++i) {
	  	var data = new IloOplDataSource("test-replace.dat");
	 	var source = new IloOplModelSource("test-replace.mod");
	 	var def = new IloOplModelDefinition(source);
	  	var cplex = new IloCplex();
		var opl = new IloOplModel(def,cplex);

	  	var data2 = new IloOplDataElements();
	  	data2.CurrentIteration = i;
	  	opl.addDataSource(data2);
	  	opl.addDataSource(data);
	  	
	 	opl.generate();
	 	cplex.solve();
	 	opl.postProcess(); 
	}
 	
	cplex.end();
}