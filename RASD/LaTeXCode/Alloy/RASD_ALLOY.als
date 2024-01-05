abstract sig User{
	name: Name,
	surname: Surname,
	nickname: Nickname,
	email: Email,
	tournaments: set Tournament,
	battles: set Battle,
	password: Password	
}


sig Student extends User{
	badges: set Badge,
	groups: set Group
}


sig Educator extends User{
}


sig Group{
	name: Name,
	members: set Student,
	highestScore: Score,
	battle: Battle,
	repo: one GitHubRepo,
}


sig Tournament{
	name: Name,
	creator: Educator,
	mods: set Educator,
	deadlineSub: Deadline,
	partecipants: set Student,
	rankings: set Student,
	stage: TournamentStage,
	battles: set Battle
}


sig Battle{
	name: Name,
	creator: Educator,
	belongsTo: Tournament,
	deadlineSubscribe: Deadline,
	deadlineSubmission: Deadline,
	manualEvaluationEnabled: Bool, 
	partecipants: set Student,
	rankings: set Group,
	kata: Kata,
	availableBadges: set Badge,
	stage: BattleStage,
	mainRepo: OriginalRepo,
	forkedRepos: set GitHubRepo,
	minPerGroup: Min,
	maxPerGroup: Max,
	automatedRules: AutomatedRules,
}


sig OriginalRepo{
	link: Link,
	battle: Battle
}


sig GitHubRepo{
	forkedFrom: OriginalRepo,
	group: Group,
	link: Link
}


sig AutomatedRules{
	securityCheckOn: Bool, 
	reliabilityCheckOn: Bool,
	maintainabilityCheckOn: Bool,
	percentageTestCasesToPass: Percentage
}


sig Badge{
	name: Name,
	variables: set Variable,
	rule: BadgeRule
}



abstract sig Name {}
abstract sig Surname {}
abstract sig Nickname {}
abstract sig Email {}
abstract sig Password {}

sig Kata{}
abstract sig Link {}
abstract sig Score {}
abstract sig Deadline {}
abstract sig Percentage {}
abstract sig Max {}
abstract sig Min {}

abstract sig TournamentStage{}
sig Subscribe extends TournamentStage{}
sig Open extends TournamentStage{}
sig Ended extends TournamentStage{}

abstract sig BattleStage{}
sig SubscribeTime extends BattleStage{}
sig GroupsCreation extends BattleStage{}
sig OpenStage extends BattleStage{}
sig EndedBattleStage extends BattleStage{}
sig Consolidation extends BattleStage{}

abstract sig Bool {}
sig True extends Bool {}
sig False extends Bool {}

sig Variable{}
sig BadgeRule{}



-----------------------------------------------------
--	FACTS					
-----------------------------------------------------



-- A Student is a participant of the battle if and only if 
-- he is listed in the set of participants of the battle.
fact StudInBattle{
	all s: Student |
		all b : Battle |
			s in b.partecipants
				iff
			b in s.battles
}



-- Every Tournament that is present in the Educator's tournaments set, 
-- must have the Educator as a mod or as the creator. 
fact EdTournamentsCorrespondence{
	all t: Tournament |
		all e: Educator |
			t in e.tournaments
				iff
			(
				e in t.mods or e = t.creator
			)
}



-- Every Tournament of the list of turnaments that the student joined, 
-- must have the same Student in the participants list of the Tournament
fact allSubscribedStudentsArePartecipants{
	all t: Tournament |
		all s: Student |
			s in t.partecipants
				iff
			t in s.tournaments
}



-- Every Battle present in the Educators' battles set must have the same Educator 
-- as the creator. The Educator must also be in the set of mods or the creator of 
-- the Tournament that the Battle belongs to.
fact EdBattleCorrespondence{
	all b: Battle |
		all e: Educator |
			b in e.battles
				iff
			(
				e = b.creator
					iff          
				(e in b.belongsTo.creator or e in b.belongsTo.mods) 
			)
}



-- Every battle that is part of a certain tournament, must have the belongsTo 
-- field set to that Tournament and the creator of the Battle must be the 
-- creator or a moderator of the Tournament
fact BattlesInTournament{
	all b: Battle |
		all t: Tournament |
			b.belongsTo = t
				iff b in t.battles iff
			(
				b.creator in t.mods  or 	b.creator in t.creator
			)
}



-- All the Battles that are part of a Tournament must be listed in the set of 
-- Battles of the Tournament.
fact BattlesInTournament{
	all b: Battle |
		all t: Tournament |
			b.belongsTo = t
				iff 
			b in t.battles
}



-- There must be no Users using the same email or password
fact noDuplicatedUsers{ 
	no disj u1, u2: User |
		u1.nickname = u2.nickname 
			or
		u1.email = u2.email
}



-- There must be no groups with the same name within a battle
fact noDuplicatedGroups{
	no disj g1, g2: Group |
		g1.battle = g2.battle 
			and
		g1.name = g2.name
}



-- Every repository used by any group partecipating to a battle
-- must be a different fork of the same initial repository created for the battle.
fact RepoConstraint{
	all disj f1, f2: GitHubRepo |
		f1.forkedFrom = f2.forkedFrom 
			iff(
				f1.group != f2.group
					and	
				f1.link != f2.link
					and
				f1.group.battle = f2.group.battle
					and
				f1.group.battle = f1.forkedFrom.battle
					and
				f1.link != f1.forkedFrom.link
			)
}



-- There must be no battles with the same name within a Tournament
fact noDuplicatedBattles{ 
	no disj b1, b2: Battle |
		b1.name = b2.name
			and
		b1.belongsTo = b2.belongsTo
}



-- There must be no Original GitHub Repositories that share the same link. 
--There must also be only one Repository for each Battle.
fact noDuplicatedOriginalRepos{
	no disj r1, r2: OriginalRepo|
		r1.battle = r2.battle
			or
		(r1.battle.mainRepo=r2)			
			or
		(r1.battle.mainRepo.link=r2.link)
}



-- There must be no Tournaments with the same name 
fact noDuplicatedTournaments{ 
	no disj t1, t2: Tournament |
		t1.name = t2.name
}



-- There must be no duplicated Forked GitHub Repository
fact noDoubleRepoLinks{
	no disj r1, r2: GitHubRepo|
		r1.link=r2.link
}



-- There must be no Groups that share the same Forked GitHub Repository
fact noMultipleGroupsShareRepo{
	no disj r1, r2: GitHubRepo|
		r1.group=r2.group
}



-- There must be no Original GitHub Repositories that share the same link 
fact noOriginalReposShareLinks{
	no disj r1, r2: OriginalRepo|
		r1.link=r2.link
}



-- There must be no Forked Repository that has the same link of any Original Repository.
fact noDoubleLinksBetweenForkedOrigina{
	all r1: OriginalRepo | 
		all r2: GitHubRepo |
			r1.link != r2.link
}



-- If a Student is a member of a Group, then the Battle that the group is subscribed 
-- to must be one of the battles that the Student had previously joined.
fact GroupStudentBattlesCorrespondence{
	all g: Group | 
		all s: Student |  
			s in g.members implies g.battle in s.battles 
}



-- There must be no Groups that have the same Forked Repository.
fact GroupsForkedReposCorrespondence{
	no disj g1, g2: Group | 
		g1.repo = g2.repo
}





-- Groups that are subscribed to the same Battle must have no Students in common.
fact noCommonStudentsInDifferentGroups{
	all disj g1, g2: Group | 
		g1.battle = g2.battle 
			implies 
		#(g1.members & g2.members) = 0 
}


-- The correlation between Students and Groups are expressed both in the 
-- members set in Group and in the groups set in Student
fact s_in_g{
	all g: Group | 
		all s: Student | 
			g in s.groups iff s in g.members
}



-- The correlation between Students and Tournaments are expressed both in the 
-- tournaments set in Student and in the participants set in Tournament
fact s_in_T{
	all s: Student | 
		all t:Tournament | 
			s in t.partecipants iff t in s.tournaments
}



-- The Students that participate to a Battle must be also 
-- participants of the Tournamnet that the Battle belongs to .
fact s_in_B_T{
	all s: Student | 
		all b: Battle | 
			b in s.battles implies s in b.belongsTo.partecipants
}



-- All the Groups that participate to a Battle 
-- must be in the Rankings of the same Battle.
fact GroupInRankings{
	all g: Group | 
		all b: Battle | 
			g.battle = b iff g in b.rankings
}



-- There must be no group without members.
fact NoEmptyGroups{
	all g: Group | 
		#(g.members) >0
}



-- The instances of the Group and their repository must be correctly linked.
fact GroupRepoConsistency{
	all g: Group | 
		all r: GitHubRepo | 
			g.repo = r iff r.group = g
}



-- The Forked Repositories mist be linked to the same Battle 
-- that their original Repositories are linked to. 
fact ForkedOriginalConsistency{
	all g: GitHubRepo | 
		all o: OriginalRepo |
			g.forkedFrom = o 
				implies 
			g in o.battle.forkedRepos
}



-- Every Student must be in a Group for every Battle he is in.
fact BattleGroupsCardinality{
	all s: Student | #s.battles =  #s.groups
}



-- Every Student must be in a Group for every Battle he is in.
fact BattleGroupsConsistency{
	all s: Student | 
		all b: Battle |
			b in s.battles 
				iff 
			one g: Group |
				b = g.battle and s in g.members
}



-- Every Battle in the Student's battles set 
-- must have the Student in the partecipant set.
fact allSubscribedStudentsArePartecipantsBattle{
	all b: Battle |
		all s: Student |
			s in b.rankings.members
				iff
			b in s.battles
				iff
			#(b.rankings & s.groups) = 1
}



-- Every Group's Repository must be a Forked Repository of the Battle's Main Repository.
fact groupReposConsistency{
	all g: Group |
		g.repo in g.battle.forkedRepos
			and
		g.repo.forkedFrom = g.battle.mainRepo
}



-- Every Group of a Student must have him listed in the set of its members.
fact StudentGroupsMembersConsistency{
	all s: Student | 
		all g: Group |
			g in s.groups 
				iff 
			( s in g.members )
}



-- Every Badge that is awarded to a Student must be one of the Badges that 
-- could be awarded in the Battles that he previously partecipated to
fact StudentsBadges{
	all s: Student |
		all b: Badge |
			b in s.badges implies b in s.battles.availableBadges
}



-- Every Forked Repository must be linked to and only to the same Battle 
-- that its Original Repository is linked to.
fact RepoLinkedToBattle{
	all r: GitHubRepo | 
		one b: Battle | 
			r in b.forkedRepos 
				and 
			b = r.forkedFrom.battle
}





-- No Battle can have the same Forked Repositories as another Battle.
fact NoCommonForkedRepos{
	no disj b1, b2: Battle | 
		#(b1.forkedRepos & b2.forkedRepos) >0
}



-----------------------------------------------------
--	ASSERTIONS					
-----------------------------------------------------



assert assertion1{
	all s: Student |
		all b: Battle |
			b in s. battles 
				implies 
			( s in b.partecipants 
				and 
			  s in b.belongsTo.partecipants 
				and 
			  b.belongsTo in s.tournaments 
				and
			 (# (s.groups & b.rankings)=1) 
			)
}
check assertion1 for 5




assert assertion2{
	all s: Student |
		all g: Group |
			s in g.members
				implies
			g in s.groups
				and
			g.battle in s.battles
				and
			g in g.battle.rankings
				and 
			s in g.battle.partecipants
				and
			#(g.battle.rankings & s.groups)=1
				and
			g.repo in g.battle.forkedRepos
				and
			g.repo.forkedFrom = g.battle.mainRepo
				and
			s in g.battle.belongsTo.partecipants
				and
			g.battle.belongsTo in s.tournaments
}
check assertion2 for 5



-----------------------------------------------------
--	PREDICATES					
-----------------------------------------------------


-- In the baseWorld there is only one Tournament, one Group, two Battles, 
-- two Students and one Educator. This is one of the simpliest possible 
-- worlds that can be generated.
pred baseWorld{
	#Tournament = 1 
	# Group = 1
	# Student = 2
	# Battle = 1
	# Educator = 1
}
run baseWorld for 5



-- In this World there is still only one Tournament, 
-- but there are three Groups of Students and there are two different Battles. 
pred World{
	#Tournament=1
	#Group = 3
	#Student>2
	#Educator>1
	#Battle = 2
	#Badge >4
	#AutomatedRules = #Battle
}
run World for 5



-- In this World there are two Tournaments, each of them having at least one Battle.
pred World2{
	#Tournament=2
		all t: Tournament | #(t.battles) >0
	#Student=4
	#Battle =2
}
run World2 for 5


