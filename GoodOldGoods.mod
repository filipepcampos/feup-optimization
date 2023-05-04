/*********************************************
 * OPL 22.1.1.0 Model
 * Author: filipe
 * Creation Date: 2 May 2023 at 05:15:22
 *********************************************/

float ExperienceWeigth = ...;
float PresentationSkillsWeigth = ...;
float LanguageSkillsWeigth = ...;
float AvailabilityWeigth = ...;
int LimitConsecutiveDays = ...;

{string} Positions = ...;
{string} PositionTypes = ...;
{string} Days = ...;
{int} CandidateIds = ...;
{string} CandidateNames = ...;
{string} SkillsTypes = ...;

int NumberOfDaySubarrays = card(Days) - LimitConsecutiveDays; // TODO: check if +1 is needed

string PositionMatch[Positions] = ...;
int LanguageSkillsMatch[Positions] = ...;
int PresentationSkillsMatch[Positions] = ...;
int Requirements[Positions][Days] = ...;
int Availability[CandidateIds][Days] = ...;
int Experience[CandidateIds][PositionTypes] = ...;
int Skills[CandidateIds][SkillsTypes] = ...;

string DayNameMatch[1..card(Days)] = ...;

dvar boolean x[Days][CandidateIds][Positions];

dexpr float capabilities = 
	sum(day in Days)
		sum(candidate in CandidateIds) 
			sum(position in Positions) 
				x[day][candidate][position] * (
					ExperienceWeigth * Experience[candidate][PositionMatch[position]] + 
						PresentationSkillsWeigth * Skills[candidate]["Presentation skills"]*PresentationSkillsMatch[position] +
						LanguageSkillsWeigth * Skills[candidate]["Language skills"]*LanguageSkillsMatch[position] +
						AvailabilityWeigth * (5 * (sum(availableDays in Days) Availability[candidate][day]) / card(Days))
				);


maximize capabilities;
 
subject to {
  	// Only 1 allocation per staff per day
  	ctSingleStaffAllocationPerDay:
		forall(day in Days)
		  forall(candidate in CandidateIds)
		    	sum(position in Positions) x[day][candidate][position] <= 1;
	
	// Only hire the exact number of required staff for each position
	ctNumberOfStaff:
		forall(day in Days)
		  forall(position in Positions)
		    	sum(candidate in CandidateIds) x[day][candidate][position] == Requirements[position][day];
	
	// Staff cannot be hired if they're not available on that day
	ctStaffIsAvailable:
		forall(day in Days)
		  forall(candidate in CandidateIds)
			    forall(position in Positions)
			      	x[day][candidate][position] <= Availability[candidate][day];
	  	
	// Maximum consecutive working days
	forall(candidate in CandidateIds)
	  forall(firstDayIndex in 1..NumberOfDaySubarrays)
	    sum(dayIndex in firstDayIndex..firstDayIndex+LimitConsecutiveDays) sum(position in Positions) x[DayNameMatch[dayIndex]][candidate][position] <=  LimitConsecutiveDays - 1;    
}

int working[c in CandidateIds][d in Days] = sum(position in Positions) x[d][c][position];
 
execute OUTPUT_RESULTS {
	var file = new IloOplOutputFile("solution.txt");
	file.writeln("Objective Function = ", cplex.getObjValue());
	
//	for(var day in Days) {
//	  file.writeln(day);
//	  
//	  for(var position in Positions){
//	    file.write("  ");
//	    file.writeln(position);
//	    
//	    for(var candidate in CandidateIds){
//	      if(x[day][candidate][position] == 1){
//	       	file.write("    ");
//	      	file.writeln(candidate) 
//	      }
//	    }
//	  }
	 for(var person in CandidateIds) {
	   for(var day in Days) {
	     file.write(working[person][day]);
	   }
	   file.writeln("--");
	}
}