abstract sig User {}

sig PolicyMaker extends User{}

sig Agronomist extends User{
    agronomistArea: one Area,
    agronomistSchedule: seq DailySchedule
}


sig Farmer extends User{
    ownedFarm: Farm,
}

sig Date{
    day: Int,
    month: Int,
    year: Int,
}{
    day     > 0 and day <= 31
    month   > 0 and month <= 12
    year    > 0
}

sig Time{
    hour: Int,
    minute: Int
}{
    hour    > 0
    minute  > 0
}

abstract sig Boolean{}
one sig True extends Boolean{}
one sig False extends Boolean{}

sig Data{}

sig GeoPosition{}

sig Farm{
    farmOwner:Farmer,
    farmArea:Area,
    farmScope: some User,
    productionData: some Data
}

sig Area{
    areaFarms: some Farm,
    areaAgronomists: some Agronomist,
    location:GeoPosition
}

sig Chat{
    chatFarmer: Farmer,
    chatAgronomist: lone Agronomist,
    chatArea: Area,
    chatScope: some User,
    chatState: ChatState
}

sig Report{
    reportAgronomist: Agronomist,
    reportVisit: Visit,
    reportData: set Data,
    reportScope: some User
}

sig Visit{
    visitAgronomist: Agronomist,
    visitFarm: Farm,
    visitDate: Date,
    visitTime: Time,
    visitScope: some User,
    visitCompleted: Boolean
}

sig DailySchedule{
    schedVisit: some Visit,
    schedDate: one Date,
    schedExamined: Boolean
}

one sig Forum{
    forumThreads: set Thread
}

sig Thread{
    threadCreator: one User,
    threadScope: some User
}

abstract sig ChatState{}
one sig Pending extends ChatState {}
one sig Opened extends ChatState {}
one sig ClosedProposed extends ChatState {}
one sig Closed extends ChatState {}

//---------------------------------------------------------------
// FACTS

fact AreasAreDisjoint{
    no disj a1,a2:Area | 
        one f:Farm |
            f in a1.areaFarms 
            and
            f in a2.areaFarms
}

fact AreasHaveDifferentLocations{
    no disj a1,a2:Area |
        a1.location = a2.location
}

fact{ //Two-way relation
    all o:Farmer, f:Farm | 
        f in o.ownedFarm iff f.farmOwner = o
}

fact{ //Two-way relation
    all ag:Agronomist, ar:Area | 
        ag in ar.areaAgronomists iff ag.agronomistArea = ar 
}

fact{ //Two-way relation
    all f:Farm, ar:Area |
        f in ar.areaFarms iff f.farmArea = ar
}

fact { //Agronomists can visit only farms that are in their area
    all v:Visit |
        v.visitAgronomist.agronomistArea = v.visitFarm.farmArea
}

fact {  //Agronomists can deal with a chat request only if the request is coming 
        //from a farm that is in their area
    all c:Chat | 
        c.chatState != Pending
        implies
        c.chatFarmer.ownedFarm.farmArea = c.chatAgronomist.agronomistArea
}

fact { //report data and production data are different 
    all r:Report, f:Farm | 
        #(r.reportData & f.productionData) = 0

}

fact ChatArea{
    all c:Chat | 
        c.chatFarmer.ownedFarm.farmArea = c.chatArea
}

fact reportAgronomist{
    all r:Report |
        r.reportAgronomist = r.reportVisit.visitAgronomist
}

fact farmScope{
    all f:Farm, pm:PolicyMaker |
        pm in f.farmScope
    
    all f:Farm, ag:Agronomist |
        ag in f.farmScope
        iff
        f.farmArea = ag.agronomistArea
    
    all f:Farm, f1:Farmer |
        f1 in f.farmScope
        iff
        f1 = f.farmOwner
}

fact threadScope{
    all t:Thread, u:User | u in t.threadScope
}

fact reportScope{
    all r:Report, pm:PolicyMaker |
        pm in r.reportScope
    
    all r:Report, a:Agronomist |
        a in r.reportScope 
        iff
        r.reportAgronomist = a
    
    all r:Report |
        no f:Farmer |
            f in r.reportScope 
}

fact chatScope{
    all c:Chat | 
        c.chatState = Pending
        implies 
        #c.chatAgronomist = 0
    
    all c:Chat |
        c.chatState = Pending
        implies
        c.chatScope = c.chatFarmer + c.chatArea.areaAgronomists
    
    all c:Chat |
        c.chatState = Opened
        implies
        c.chatScope = c.chatFarmer + c.chatAgronomist
        
    all c:Chat |
        c.chatState = Closed
        implies
        c.chatScope = c.chatFarmer + c.chatAgronomist
    
    all c:Chat |
        c.chatState = ClosedProposed
        implies
        c.chatScope = c.chatFarmer + c.chatAgronomist
}

fact visitScope{
    all v:Visit, pm:PolicyMaker |
        pm in v.visitScope
    
    all v:Visit |
        v.visitAgronomist in v.visitScope
    
    all v:Visit |
        v.visitFarm.farmOwner in v.visitScope
}

fact dailySchedule{
    //Visits in the daily schedule have the same date of the daily schedule 
    all ds:DailySchedule, v:Visit | 
        v in ds.schedVisit 
        implies
        v.visitDate = ds.schedDate
    
    //schedExamined means that the agronomist has "confirmed" 
    //the daily schedule in the system: so a report must be inserted
    all ds:DailySchedule, v:Visit | ds.schedExamined = True
        implies
            (v in ds.schedVisit and v.visitCompleted = True
            implies
            one r:Report | r.reportVisit = v)
    
    // There cannot be two unexamined schedules: 
    // the agronomist has to confirm their schedule
    // at most at the end of the day!
    all ag:Agronomist, ds:DailySchedule | 
        (ds in ag.agronomistSchedule.elems and ds.schedExamined = False ) 
        implies
        ds = ag.agronomistSchedule.last  
    
    // There are no daily schedules belonging to nobody
    all ds:DailySchedule | some ag:Agronomist | ds in ag.agronomistSchedule.elems

    // Each daily schedule is personal
    no disj ag1, ag2: Agronomist | ag1.agronomistSchedule = ag2.agronomistSchedule
    
    all ds:DailySchedule|
        no disj ag1, ag2: Agronomist|
            ( ds in ag1.agronomistSchedule.elems)
            and
            ( ds in ag2.agronomistSchedule.elems)


    all  ag:Agronomist | !ag.agronomistSchedule.hasDups
}

fact visitAgronomist{
    // If there is a visit, it is inserted in one of the agronomists'schedule
    all v:Visit, ag:Agronomist |
        ag = v.visitAgronomist 
        iff
        v in ag.agronomistSchedule.elems.schedVisit
}

fact{
    //There cannot be two different visit that happened in the same instant
    all ag:Agronomist | 
        no disj v1,v2 :Visit |
            (v1 in ag.agronomistSchedule.elems.schedVisit 
            and v1.visitCompleted = True)
            and
            (v2 in ag.agronomistSchedule.elems.schedVisit 
            and v2.visitCompleted = True)
            and
            (v1.visitDate = v2.visitDate 
            and v1.visitTime = v2.visitTime)
}

fact{
    //Each daily schedule is in fact unique for each day
    //Since the schedule of the agronomist is a sequence of daily schedules
    //the visits in the daily schedules reflect the same order 
    all ag: Agronomist |
        no disj ds1, ds2 : DailySchedule | 
            ds1 in ag.agronomistSchedule.elems
            and
            ds2 in ag.agronomistSchedule.elems
            and
            ds1.schedDate = ds2.schedDate

    all ag:Agronomist, ds1, ds2:DailySchedule | 
        (ds1 in ag.agronomistSchedule.elems
        and
        ds2 in ag.agronomistSchedule.elems 
        and
        ag.agronomistSchedule.idxOf[ds2] > ag.agronomistSchedule.idxOf[ds1])
        implies
        isSuccDate[ds1.schedDate, ds2.schedDate]

}

fact {
    // A report can be generated only if a visit has been completed
    all r:Report, v:Visit | v in r.reportVisit iff v.visitCompleted = True
}

//---------------------------------------------------------------
// PREDICATES

pred isSuccDate[d1:Date, d2:Date]{
    d2.year > d1.year
    or
    (
        d2.year = d1.year
        and
        d2.month > d1.month
    )
    or
    (
        d2.year = d1.year
        and
        d2.month = d1.month
        and
        d2.day > d1.day
    )
}

pred show {
    #User > 2
    #Chat = 1
    #Agronomist = 1
    #PolicyMaker = 1
    #Farmer = 2
    #Visit  = 1
    #Thread = 0
    #DailySchedule = 1

}
run show for 5 but 6 int

pred scheduleExamined[ds:DailySchedule, v:Visit]{
    //This predicate shows that if a schedule has been examined
    //visits that have been completed have an associated report
    ds.schedExamined = True
    v in ds.schedVisit
    v.visitCompleted = True
    #Visit > 2
}

run scheduleExamined for 3 but 6 int

pred showScope
    [disj a1,a2:Area,ds:DailySchedule, v:Visit, disj f1,f2:Farm,
    disj agr1, agr2:Agronomist, pm1:PolicyMaker]
{
    //This predicate shows what can be seen by the different Users
    f1.farmArea = a1
    f2.farmArea = a2
    agr1.agronomistArea = a1
    agr2.agronomistArea = a2
    ds.schedExamined = True
    v in ds.schedVisit
    v.visitCompleted = True
    ds in agr1.agronomistSchedule.elems

}

run showScope for 5 but 6 int

pred chatPending[c:Chat, f:Farmer, disj a1,a2:Area,
disj ag1,ag2,ag3:Agronomist,state:Pending]{
    c.chatFarmer = f
    c.chatState = state
    c.chatArea = a1
    f.ownedFarm.farmArea = a1
    ag1.agronomistArea = a1
    ag2.agronomistArea = a1
    ag3.agronomistArea = a2
    
}
run chatPending for 5 but 6 int 


pred newVisit[v:Visit, ag1:Agronomist, ds:DailySchedule]{
    #Chat = 0
    ds in ag1.agronomistSchedule.elems
    v.visitAgronomist = ag1
    ds.schedVisit = ds.schedVisit + v
}

run newVisit for 5 but 6 int


//---------------------------------------------------------------
// ASSERTIONS

assert OneOwner {
   no disj f1,f2: Farmer | f1.ownedFarm = f2.ownedFarm 
}
check OneOwner

assert AgronomistsRespectArea{
    no v:Visit |
        v.visitAgronomist.agronomistArea != v.visitFarm.farmArea
    and
    no c:Chat | 
        c.chatAgronomist.agronomistArea != c.chatFarmer.ownedFarm.farmArea
}
check AgronomistsRespectArea for 5 but 6 int

assert AgronomistOperatingArea{
    all ag:Agronomist, ds1, ds2 : DailySchedule|
        no disj v1, v2: Visit |
            ds1 in ag.agronomistSchedule.elems
            and 
            ds2 in ag.agronomistSchedule.elems
            and
            v1 in ds1.schedVisit
            and 
            v2 in ds2.schedVisit
            and
            v1.visitFarm.farmArea != v2.visitFarm.farmArea

    no disj ag1,ag2:Agronomist, ds1:DailySchedule|
        all v:Visit |
            ds1 in ag1.agronomistSchedule.elems
            and
            v in ds1.schedVisit
            and
            v.visitAgronomist = ag2
            
}

check AgronomistOperatingArea for 5 but 6 int


assert PolicyMakerSeeEveryFarm{
    all pm:PolicyMaker, f:Farm |
        pm in f.farmScope
    all pm:PolicyMaker, r:Report | 
        pm in r.reportScope
    all pm:PolicyMaker, v:Visit | 
        pm in v.visitScope
    all pm:PolicyMaker, t:Thread | 
        pm in t.threadScope
        
}
check PolicyMakerSeeEveryFarm for 5 but 6 int