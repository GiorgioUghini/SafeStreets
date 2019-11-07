/***************DOMAIN ASSUMPTIONS***************/
sig Email {} {
    //each email belongs to 1 customer only
    one u: Customer | this = u.email
}
sig Password {} {
    //A password must belong to a customer, but different customers can have the same pwd
    some u: Customer | this = u.password
}

//either a user or an officer
abstract sig Customer{
    email: one Email,
    password: one Password
}

sig User extends Customer {
    reports: set Violation
}
sig Officer extends Customer{
    handledViolations: set Violation
} {
    //officers handle only violations without ticket
    all v : handledViolations | v.ticket = none
}

//The police system of a city
sig LocalPolice{
    officers: set Officer,
    violations: set Violation,
    accidents: set Accident,
    positions: set Position,
    unsafePositions: set UnsafePosition,
    confirmedTickets: set Violation
}


sig LicensePlate {} { 
    //all licensePlates must belong to a picture
    some p: Picture | this = p.licensePlate 
}

sig Ticket {} { 
    // all tickets, pictures and positions must belong to a violation
    one v: Violation | this = v.ticket 
}
sig Position {} { 
    //all position must belong to a violation
    some v: Violation | this = v.position
}
sig Picture {
    licensePlate: lone LicensePlate
} { 
    //each picture must belong to exactly one violation
    one v: Violation | this in v.pictures
}

//a violation type can belong to no violation
sig ViolationType{}

sig Violation {
    violationType: one ViolationType,
    position: one Position,
    ticket: lone Ticket,
    pictures: set Picture
} {
    //a violation must belong to only one user
    one u: User | this in u.reports
}

//An accident registered in the police system
sig Accident {
    position: one Position,
    accidentType: one AccidentType
} {
    //all accidents must belong to one and only one local police
    one p: LocalPolice | this in p.accidents
}

sig AccidentType {} { 
    //an accidentType must belong to an accident
    some a: Accident | this in a.accidentType
}

//The core of the suggestions given by the system
sig UnsafeReason {
    accType: one AccidentType,
    violType: one ViolationType,
    suggestion: one Suggestion
}

sig UnsafePosition{
    reasons: set UnsafeReason,
    position: one Position
}

sig Suggestion {} {
    //every suggestion belongs to an unsafe position
    some u: UnsafeReason | this = u.suggestion
}

abstract sig AbstrHashes {
    hashes: Violation -> Hash
}

//The hashes calculated by the SafeStreet System
one sig Hashes extends AbstrHashes {}

//The hashes calculated by the police system
one sig PoliceHashes extends AbstrHashes {}

sig Hash{} {
    //A hash must belong to either a system hash or a police hash
    some h: AbstrHashes |
        this in Violation.(h.hashes)
}

//a violation must have exactly one license plate
fact {
    all v: Violation | #v.pictures.licensePlate = 1
}

/* An UnsafePosition must belong to a position iff its violation and accident
happened at least 2 times in that location */
//NB: 2 is a really low number used to make the model work, it is not the actual number
fact {
    all u: UnsafePosition | some p: Position, vt: ViolationType, at: AccidentType, r: UnsafeReason |
        p = u.position and r in u.reasons and vt = r.violType and at = r.accType and
        #{v: Violation | v.position = p and vt = v.violationType} > 1 and
        #{a: Accident | a.position = p and at = a.accidentType} > 1
}

//2 unsafePositions cannot have the same reason and position
fact {
    no disj up1, up2 : UnsafePosition | some ur: UnsafeReason, p: Position |
        ur in up1.reasons and ur in up2.reasons
        and p = up1.position and p = up2.position
}

//2 unsafeReason cannot have the same accident type and violation type
fact {
    no disj ur1, ur2: UnsafeReason | ur1.accType = ur2.accType and
        ur1.violType = ur2.violType
}

//all positions, accidents, violations and officers must belong to 1 and only 1 localPolice
fact {
    all p: Position | one lp: LocalPolice | p in lp.positions
    all o: Officer | one lp: LocalPolice | o in lp.officers
    all v: Violation | one lp: LocalPolice | v in lp.violations
    all a: Accident | one lp: LocalPolice | a in lp.accidents
}

//a violation belongs to a local police iff its position is one of the local police positions
fact {
    all v: Violation | all lp: LocalPolice |
        v.position in lp.positions <=> v in lp.violations
}

//a violation can be handled by an officer only
fact {
    all v: Violation | no disj o1,o2: Officer |
        v in o1.handledViolations and v in o2.handledViolations
}

//an unsafePositions must belong to the LocalPolice that has its position
fact{
    all up: UnsafePosition | all lp: LocalPolice |
        (up in lp.unsafePositions) <=> (up.position in lp.positions)
}

/* a ticket is confirmed iff its hash on the police system matches the one on
the SafeStreet System */
fact {
    all v: Violation | v in LocalPolice.confirmedTickets iff
        v.(Hashes.hashes) = v.(PoliceHashes.hashes)
}

//A violation can be in confirmedTickets only if it has a ticket 
fact {
    no v: Violation | v in LocalPolice.confirmedTickets and v.ticket = none
}

//all violations have their hash on SafeStreet System
fact {
    all v: Violation | one h: Hash | v->h in Hashes.hashes
}

//a violation cannot have more than 1 hash on the police system
fact {
    all v: Violation | #v.(PoliceHashes.hashes) <= 1
}

//Violations without tickets do not have an hash
fact {
    all v: Violation | v.ticket = none implies v !in PoliceHashes.hashes.Hash
}

//2 violations cannot have the same hash
fact {
    no disj v1,v2 : Violation | some h: Hash |
        v1->h in Hashes.hashes and v2->h in Hashes.hashes
}

//for a localPolice to confirm a ticket it must be in its violations
fact {
    all lp: LocalPolice | all v: Violation | v in lp.confirmedTickets implies v in lp.violations
}

/*******************ASSERTIONS*******************/
//2 localPolice cannot have the same violation
check {
    no disj lp1, lp2: LocalPolice |
        some v: Violation | v in lp1.violations and v in lp2.violations
}

//a unsafePosition cannot belong to 2 different localPolice
check {
    all up: UnsafePosition | one lp: LocalPolice | up in lp.unsafePositions
}

//a violation cannot appear 2 times in the hashes system
check{
    all v: Violation | #v.(Hashes.hashes) = 1
}

//if a LocalPolice has a confirmedTicket it must have at its position
check {
    all lp: LocalPolice | all v: Violation | v in lp.confirmedTickets implies v.position in lp.positions
}

/*******************PREDICATES*******************/

pred world1{
    #LocalPolice = 2
    all lp: LocalPolice | #lp.violations>0
    #LicensePlate > 1
    #User = 2
    #Officer = 1
    all u: User | u.reports != none
}

pred world2{
    #Suggestion = 2
    all u: UnsafeReason | some up: UnsafePosition |
        u in up.reasons
    #confirmedTickets = 0
}

pred world3 {
    #confirmedTickets > 0
    #Ticket > #confirmedTickets
    #Violation > #Ticket
    #LocalPolice = 2
    all lp: LocalPolice | lp.violations != none
    #Accident = 0
    #AccidentType = 0
}

run world1 for 5
run world2 for 5
run world3 for 5