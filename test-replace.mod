/*********************************************
 * OPL 22.1.1.0 Model
 * Author: filipe
 * Creation Date: 9 May 2023 at 17:50:34
 *********************************************/

// === PARAMETERS ===========================================================================

string CurrentDay = ...;
int CurrentIteration = ...;
{int} MissingStaffSet[1..900] = ...;
{int} MissingStaff = MissingStaffSet[CurrentIteration];

float ExperienceWeigth = ...;
float PresentationSkillsWeigth = ...;
float LanguageSkillsWeigth = ...;
assert ExperienceWeigth + PresentationSkillsWeigth + LanguageSkillsWeigth == 1.0;

int MaximumConsecutiveDays = ...;

int TargetNumberOfWorkers = ...;
int MaximumNumberOfWorkers = ...;
float PenaltyPerExtraWorker = ...;
assert TargetNumberOfWorkers <= MaximumNumberOfWorkers;

// ==========================================================================================

// === DATA =================================================================================
{string} PositionsWithWaitingList = ...;
{string} Positions = {p | p in PositionsWithWaitingList : p != "Waiting List " };
{string} PositionTypes = ...;
{string} Days = ...;
{int} CandidateIds = ...;
string CandidateNames[CandidateIds] = ...;
{string} SkillsTypes = ...;

int NumberOfDays = card(Days);
int NumberOfDaySubarrays = NumberOfDays - MaximumConsecutiveDays - 1;

string PositionMatch[Positions] = ...;
int LanguageSkillsMatch[Positions] = ...;
int PresentationSkillsMatch[Positions] = ...;
int Requirements[PositionsWithWaitingList][Days] = ...;
int Availability[CandidateIds][Days] = ...;
int Experience[CandidateIds][PositionTypes] = ...;
int Skills[CandidateIds][SkillsTypes] = ...;
string DayNameMatch[1..NumberOfDays] = ...;

int PreviousAssignments[Days][CandidateIds][PositionsWithWaitingList] = ...;

// ==========================================================================================

dvar boolean x[Days][CandidateIds][Positions];
dvar float+ slack_number_of_workers;

// === REGULAR ALLOCATIONS ==================================================================

dexpr float number_of_workers = 
	sum(candidate in CandidateIds)
	  	((sum(day in Days) sum(position in Positions) x[day][candidate][position]) >= 1);

dexpr float capabilitiesArray[position in Positions][candidate in CandidateIds] =
		(
				ExperienceWeigth * Experience[candidate][PositionMatch[position]] + 
					PresentationSkillsWeigth * Skills[candidate]["Presentation skills"] * PresentationSkillsMatch[position] +
					LanguageSkillsWeigth * Skills[candidate]["Language skills"] * LanguageSkillsMatch[position] +
					// If presentation or language skills are not required, then experience should have their weight
					(1-LanguageSkillsMatch[position]) * LanguageSkillsWeigth * Experience[candidate][PositionMatch[position]] +
					(1-PresentationSkillsMatch[position]) * PresentationSkillsWeigth * Experience[candidate][PositionMatch[position]]
		);

dexpr float capabilitiesPerAllocation[day in Days][position in Positions] =
	sum(candidate in CandidateIds) (
		x[day][candidate][position] * capabilitiesArray[position][candidate]
	);

dexpr float capabilitiesPerDay[day in Days] = (
	sum(position in Positions : Requirements[position][day] > 0)
		capabilitiesPerAllocation[day][position] / Requirements[position][day]
	) / card(PositionsWithWaitingList);

dexpr float capabilities = ( 
	sum(day in Days)
		capabilitiesPerDay[day]
	) / card(Days);
	
dexpr float regularAllocations = 
	capabilities
	- slack_number_of_workers * PenaltyPerExtraWorker;
	
dexpr float capabilitiesOfReplacements =
	sum(candidate in CandidateIds : PreviousAssignments[CurrentDay][candidate]["Waiting List "] == 1)(
		(sum(position in Positions) x[CurrentDay][candidate][position]*capabilitiesArray[position][candidate])
	) / card(MissingStaff);
	
dexpr float travelTimeOfReplacements =
	sum(candidate in CandidateIds : PreviousAssignments[CurrentDay][candidate]["Waiting List "] == 1)(
		(sum(position in Positions) x[CurrentDay][candidate][position])*Skills[candidate]["Travel time&distance"]
	) / card(MissingStaff);
// ==========================================================================================

maximize regularAllocations; 

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
	forall(candidate in CandidateIds) {
	 	forall(firstDayIndex in 1..NumberOfDaySubarrays)
		    sum(dayIndex in firstDayIndex..firstDayIndex+MaximumConsecutiveDays+1) 
		    	sum(position in Positions) 
		    		x[DayNameMatch[dayIndex]][candidate][position] <=  MaximumConsecutiveDays; 
	}
	
	// Limit number of workers
	number_of_workers <= TargetNumberOfWorkers + slack_number_of_workers;
 	slack_number_of_workers <= MaximumNumberOfWorkers - TargetNumberOfWorkers;
	
	// Only make changes to the CurrentDay, keep the other as they were
	forall(day in Days : day != CurrentDay)
	  forall(candidate in CandidateIds)
	    forall(position in Positions)
	  		x[day][candidate][position] == PreviousAssignments[day][candidate][position];
	 
	// If candidates are currently assigned they cannot be "moved"
	forall(candidate in CandidateIds : candidate not in MissingStaff)
	  forall(position in Positions)
	  	if(PreviousAssignments[CurrentDay][candidate][position] > 0)
	  		x[CurrentDay][candidate][position] == 1;
	
	// If staff is missing, then they cannot work (obviously)
	forall(candidate in CandidateIds : candidate in MissingStaff)
	  forall(position in Positions)
	    x[CurrentDay][candidate][position] == 0;
	    
	// If staff wasn't working and isn't on waiting list, then cannot be assigned
	forall(candidate in CandidateIds : candidate not in MissingStaff)
	  forall(position in Positions)
	    if(PreviousAssignments[CurrentDay][candidate][position] == 0 && 
	    	PreviousAssignments[CurrentDay][candidate]["Waiting List "] == 0)
	    	x[CurrentDay][candidate][position] == 0;
}


// Some metrics to help understand our solution:
// Average availability in percentage of total days (0 to 1)
dexpr float availability_percentage = (
	sum(candidate in CandidateIds) (
	  (sum(day in Days) Availability[candidate][day]) / NumberOfDays
	)
) / card(CandidateIds);

// Average experience in percentage
dexpr float experience_percentage = sum(day in Days) ((
		sum(position in Positions : Requirements[position][day] > 0) (
			sum(candidate in CandidateIds) (
				(x[day][candidate][position] * Experience[candidate][PositionMatch[position]])
			)
		)
	) /	(
	sum(position in Positions)
	  Requirements[position][day]
	)) / NumberOfDays;

// Language skills average
{string} PositionsWithLanguageSkillsPerDay[day in Days] = {p | p in Positions : LanguageSkillsMatch[p] > 0 && Requirements[p][day] > 0 };
dexpr float language_skills_percentage = 
	sum(day in Days) (
		sum(position in PositionsWithLanguageSkillsPerDay[day]) (
		  		sum(candidate in CandidateIds) (
					x[day][candidate][position] * Skills[candidate]["Language skills"] * LanguageSkillsMatch[position]
				) / Requirements[position][day] 
		) / card(PositionsWithLanguageSkillsPerDay[day])
	) / card(Days);

// Presentation skills average
{string} PositionsWithPresentationSkillsPerDay[day in Days] = {p | p in Positions : PresentationSkillsMatch[p] > 0 && Requirements[p][day] > 0 };
dexpr float presentation_skills_percentage = 
	sum(day in Days) (
		sum(position in PositionsWithPresentationSkillsPerDay[day]) (
		  		sum(candidate in CandidateIds) (
					x[day][candidate][position] * Skills[candidate]["Presentation skills"] * PresentationSkillsMatch[position]
				) / Requirements[position][day] 
		) / card(PositionsWithPresentationSkillsPerDay[day])
	) / card(Days);


execute OUTPUT_RESULTS_LOG {
	var file = new IloOplOutputFile("replace_solution.txt");
	file.writeln("Objective Function = ", cplex.getObjValue());
	file.writeln("Average Availability = ", availability_percentage * NumberOfDays, " days");
	file.writeln("Average Experience = ", experience_percentage, " / 5");
	file.writeln("Average Language Skills (for positions that require it) = ", language_skills_percentage, " / 5");
	file.writeln("Average Presentation Skills (for positions that require it) = ", presentation_skills_percentage, " / 5");
	file.writeln("Average Capability of Replacements = ", capabilitiesOfReplacements);
	file.writeln("Average Travel time of Replacements = ", travelTimeOfReplacements);
	
	file.writeln("\nAllocations:\n");
	
	for(var day in Days) {
	  file.writeln(day);
	  
	  for(var position in Positions){
	    file.write("    ");
	    file.writeln(position);
	    
	    for(var candidate in CandidateIds){
	      if(x[day][candidate][position] == 1){
	       	file.write("        ");
	      	file.writeln(candidate, ":", CandidateNames[candidate], " - ", Experience[candidate][PositionMatch[position]]); 
	      }
	    }
	  }
 	}
}

execute OUTPUT_REPLACEMENT_METRICS {
  	writeln("Solved iteration ", CurrentIteration, " with obj=", cplex.getObjValue());	
  	var file = new IloOplOutputFile("test_replace_metrics.txt", true);
  	file.writeln(cplex.getObjValue(), ",", capabilitiesOfReplacements, ",", travelTimeOfReplacements);
}
