/*********************************************
 * OPL 22.1.1.0 Model
 * Author: filipe
 * Creation Date: 2 May 2023 at 05:15:22
 *********************************************/

// === PARAMETERS ===========================================================================
float ExperienceWeigth = ...;
float PresentationSkillsWeigth = ...;
float LanguageSkillsWeigth = ...;
assert ExperienceWeigth + PresentationSkillsWeigth + LanguageSkillsWeigth == 1.0;

float WaitingListCapabilityWeigth = ...;
float WaitingListTravelWeigth = ...;

// Number of days in a row, d: 0 <= d <= Acceptable (no penalty), Acceptable < d <= Maximum (penalty per extra day)
int AcceptableConsecutiveDays = ...;
int MaximumConsecutiveDays = ...;
float PenaltyPerExtraConsecutiveDay = ...;
assert AcceptableConsecutiveDays <= MaximumConsecutiveDays;

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
int NumberOfDaySubarrays = NumberOfDays - AcceptableConsecutiveDays;

string PositionMatch[Positions] = ...;
int LanguageSkillsMatch[Positions] = ...;
int PresentationSkillsMatch[Positions] = ...;
int Requirements[PositionsWithWaitingList][Days] = ...;
int Availability[CandidateIds][Days] = ...;
int Experience[CandidateIds][PositionTypes] = ...;
int Skills[CandidateIds][SkillsTypes] = ...;
string DayNameMatch[1..NumberOfDays] = ...;

// ==========================================================================================

dvar boolean x[Days][CandidateIds][PositionsWithWaitingList];
dvar float+ slack_number_of_workers;
dvar float+ slack_consecutive_days[CandidateIds];

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
	) / card(Positions);

dexpr float capabilities = ( 
	sum(day in Days)
		capabilitiesPerDay[day]
	) / card(Days);
	
dexpr float regularAllocations = 
	capabilities 
	- slack_number_of_workers * PenaltyPerExtraWorker
	- (sum(candidate in CandidateIds) slack_consecutive_days[candidate]) * PenaltyPerExtraConsecutiveDay;
	
// ==========================================================================================


// === WAITING LIST  ALLOCATIONS ============================================================


dexpr float waitingListTravel =
	sum(day in Days) (
		sum(candidate in CandidateIds) (
			x[day][candidate]["Waiting List "] * Skills[candidate]["Travel time&distance"]
		) / Requirements["Waiting List "][day]
	) / card(Days);
	
dexpr float averageWaitingListCapability =
	sum(day in Days)(
		sum(position in Positions) (
	    	sum(candidate in CandidateIds)
	    		x[day][candidate]["Waiting List "] * capabilitiesArray[position][candidate]
		) / Requirements["Waiting List "][day] / card(Positions)
	) / card(Days);

dexpr float waitingListAllocations = 
	WaitingListCapabilityWeigth *averageWaitingListCapability + 
	WaitingListTravelWeigth * waitingListTravel;

// ==========================================================================================

maximize staticLex(regularAllocations, waitingListAllocations); 

subject to {
  	// Only 1 allocation per staff per day
  	ctSingleStaffAllocationPerDay:
		forall(day in Days)
		  forall(candidate in CandidateIds)
		    	sum(position in PositionsWithWaitingList) x[day][candidate][position] <= 1;
	
	// Only hire the exact number of required staff for each position
	ctNumberOfStaff:
		forall(day in Days)
		  forall(position in PositionsWithWaitingList)
		    	sum(candidate in CandidateIds) x[day][candidate][position] == Requirements[position][day];
	
	// Staff cannot be hired if they're not available on that day
	ctStaffIsAvailable:
		forall(day in Days)
		  forall(candidate in CandidateIds)
			    forall(position in PositionsWithWaitingList)
			      	x[day][candidate][position] <= Availability[candidate][day];
	  	
	// Maximum consecutive working days
	forall(candidate in CandidateIds) { 
	  	slack_consecutive_days[candidate] <= MaximumConsecutiveDays - AcceptableConsecutiveDays;
	  	
	 	forall(firstDayIndex in 1..NumberOfDaySubarrays)
		    sum(dayIndex in firstDayIndex..firstDayIndex+AcceptableConsecutiveDays) 
		    	sum(position in Positions) 
		    		x[DayNameMatch[dayIndex]][candidate][position] <=  AcceptableConsecutiveDays - 1 + slack_consecutive_days[candidate]; 
	}
	
	// Limit number of workers
	number_of_workers <= TargetNumberOfWorkers + slack_number_of_workers;
 	slack_number_of_workers <= MaximumNumberOfWorkers - TargetNumberOfWorkers;
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
	var file = new IloOplOutputFile("solution.txt");
	file.writeln("Objective Function Z1 = ", cplex.getObjValue());
	file.writeln("Objective Function Z2 = ", waitingListAllocations);
	file.writeln("Average Availability = ", availability_percentage * NumberOfDays, " days");
	file.writeln("Average Experience = ", experience_percentage, " / 5");
	file.writeln("Average Language Skills (for positions that require it) = ", language_skills_percentage, " / 5");
	file.writeln("Average Presentation Skills (for positions that require it) = ", presentation_skills_percentage, " / 5");
	file.writeln("Number of workers = ", number_of_workers);
	
	file.writeln("\nAllocations:\n");
	
	for(var day in Days) {
	  file.writeln(day);
	  
	  for(var position in PositionsWithWaitingList){
	    file.write("    ");
	    file.writeln(position);
	    
	    for(var candidate in CandidateIds){
	      if(x[day][candidate][position] == 1){
	       	file.write("        ");
	       	if(position == "Waiting List ")
	      		file.writeln(candidate, ":", CandidateNames[candidate]);
	      	else
	      		file.writeln(candidate, ":", CandidateNames[candidate], " - ", Experience[candidate][PositionMatch[position]]);
	      }
	    }
	  }
 	}
}

execute OUTPUT_DECISION_VARIABLE {
  var file = new IloOplOutputFile("decision.txt");
  file.writeln(x);
}

execute OUTPUT_CSV {
  var file = new IloOplOutputFile("allocations.csv");
  
  
  file.writeln("Day,Position,Position Type,Candidate Id,Candidate Name,Experience,Language Skills,Presentation Skills");
  
  for(var day in Days) {
    for(var position in PositionsWithWaitingList) {
      for(var candidate in CandidateIds) {
        if(x[day][candidate][position] == 1){
            var languageSkill = Skills[candidate]["Language skills"];
            var presentationSkill = Skills[candidate]["Presentation skills"];
          	if(position == "Waiting List ") {
          	  file.writeln(day,",",position,",Waiting List,",candidate,",",CandidateNames[candidate],",0,",languageSkill,",",presentationSkill);
          	} else {
          	 	var experience = Experience[candidate][PositionMatch[position]];
	            file.writeln(day,",",position,",",PositionMatch[position],",",candidate,",",CandidateNames[candidate],",",experience,",",languageSkill,",",presentationSkill); 
          	}
          }        
      }
    }
  }
}
