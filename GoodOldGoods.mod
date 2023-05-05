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
string CandidateNames[CandidateIds] = ...;
{string} SkillsTypes = ...;

int NumberOfDays = card(Days);
int NumberOfDaySubarrays = NumberOfDays - LimitConsecutiveDays; // TODO: check if +1 is needed

string PositionMatch[Positions] = ...;
int LanguageSkillsMatch[Positions] = ...;
int PresentationSkillsMatch[Positions] = ...;
int Requirements[Positions][Days] = ...;
int Availability[CandidateIds][Days] = ...;
int Experience[CandidateIds][PositionTypes] = ...;
int Skills[CandidateIds][SkillsTypes] = ...;

string DayNameMatch[1..NumberOfDays] = ...;

dvar boolean x[Days][CandidateIds][Positions];

// ======================= METRICS =======================		
// Average availability in percentage of total days (0 to 1)
dexpr float kpi_availability = (
	sum(candidate in CandidateIds) (
	  (sum(day in Days) Availability[candidate][day]) / NumberOfDays
	)
) / card(CandidateIds);

// Average experience in percentage (0 to 1)
dexpr float kpi_experience = sum(day in Days) ((
		sum(position in Positions : Requirements[position][day] > 0) (
			sum(candidate in CandidateIds) (
				(x[day][candidate][position] * Experience[candidate][PositionMatch[position]]) / 5
			)
		)
	) /	(
	sum(position in Positions)
	  Requirements[position][day]
	)) / NumberOfDays;

// Number of workers
dexpr float kpi_number_of_workers = 
	sum(candidate in CandidateIds)
	  	minl(1, sum(day in Days) sum(position in Positions) x[day][candidate][position]);
// ======================= END OF METRICS =======================

dexpr float capabilities = 
	sum(day in Days)
		sum(candidate in CandidateIds) 
			sum(position in Positions) 
				x[day][candidate][position] * (
					ExperienceWeigth * Experience[candidate][PositionMatch[position]] + 
						PresentationSkillsWeigth * Skills[candidate]["Presentation skills"]*PresentationSkillsMatch[position] +
						LanguageSkillsWeigth * Skills[candidate]["Language skills"]*LanguageSkillsMatch[position] +
						AvailabilityWeigth * (5 * (sum(availableDays in Days) Availability[candidate][day]) / NumberOfDays)
				);

dexpr float regularAllocations = capabilities;
dexpr float waitingListAllocations = 0;

maximize regularAllocations;
//maximize staticLex(regularAllocations, waitingListAllocations);
 
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
 
execute OUTPUT_RESULTS_LOG {
	var file = new IloOplOutputFile("solution.txt");
	file.writeln("Objective Function = ", cplex.getObjValue());
	file.writeln("Average Availability = ", kpi_availability * NumberOfDays, " days");
	file.writeln("Average Experience = ", kpi_experience * 5, " / 5");
	file.writeln("Number of workers = ", kpi_number_of_workers);
	
	file.writeln("\nAllocations:\n");
	
	for(var day in Days) {
	  file.writeln(day);
	  
	  for(var position in Positions){
	    file.write("    ");
	    file.writeln(position);
	    
	    for(var candidate in CandidateIds){
	      if(x[day][candidate][position] == 1){
	       	file.write("        ");
	      	file.writeln(CandidateNames[candidate], " - ", Experience[candidate][PositionMatch[position]]); 
	      }
	    }
	  }
 	}
}

execute OUTPUT_CSV {
  var file = new IloOplOutputFile("allocations.csv");
  
  
  file.writeln("Day,Position,Candidate Id,Experience,Language Skills,Presentation Skills");
  
  for(var day in Days) {
    for(var position in Positions) {
      for(var candidate in CandidateIds) {
        if(x[day][candidate][position] == 1){
	        var experience = Experience[candidate][PositionMatch[position]];
	        var languageSkill = Skills[candidate]["Language skills"];
	        var presentationSkill = Skills[candidate]["Presentation skills"];
	        file.writeln(day,",",position,",",candidate,",",experience,",",languageSkill,",",presentationSkill);
      	}        
      }
    }
  }
}