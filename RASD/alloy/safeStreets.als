/***************DOMAIN ASSUMPTIONS***************/
sig Email {} {one u: Customer | this = u.email}
sig Password {} {some u: Customer | this = u.password}

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
sig LocalPolice{
    officers: set Officer,
    violations: set Violation,
    accidents: set Accident,
    positions: set Position,
    unsafePositions: set UnsafePosition,
    confirmedTickets: set Violation
}

//all licensePlates must belong to a picture
sig LicensePlate {} { some p: Picture | this = p.licensePlate }
// all tickets, pictures and positions must belong to a violation
sig Ticket {} { one v: Violation | this = v.ticket }
sig Position {} { some v: Violation | this = v.position }
sig Picture {
    licensePlate: lone LicensePlate
} { one v: Violation | this in v.pictures }

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

//The hashes calculated by the SafeStreet System
one sig Hashes{
    hashes: Violation -> Hash
}

//The hashes calculated by the police system
one sig PoliceHashes{
    hashes: Violation -> Hash
}

sig Hash{} {
    //A hash must belong to either a system hash or a police hash
    some h1: Hashes, h2: PoliceHashes |
        this in Violation.(h1.hashes) or this in Violation.(h2.hashes)
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

fact {
    no disj up1, up2 : UnsafePosition | some ur: UnsafeReason, p: Position |
        ur in up1.reasons and ur in up2.reasons
        and p = up1.position and p = up2.position
}

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

/********************FUNCTIONS*******************/
fun getViolationsByPosition[p: Position] : set Violation {
    {v: Violation | v.position = p}
}
fun getAccidentsByPosition[p: Position]: set Accident{
    {a: Accident | a.position = p}
}
fun getLicensePlate[v: Violation] : one LicensePlate {
    let x = {p: Picture | p in v.pictures and #p.licensePlate=1} |
        x.licensePlate
}

/******************ASSERTIONS******************/

//2 localPolice cannot have the same violation
check {
    no disj lp1, lp2: LocalPolice |
        some v: Violation | v in lp1.violations and v in lp2.violations
}

//a report cannot belong to 2 users
check {
    no disj u1, u2: User | some v: Violation | v in u1.reports and v in u2.reports
} for 5

//2 users cannot have same email
check {
    no disj c1, c2: Customer | c1.email = c2.email
} for 5

check {
    no up: UnsafePosition | some disj p1, p2: LocalPolice |
        up in p1.unsafePositions and up in p2.unsafePositions
}

pred show{
    #LocalPolice.confirmedTickets > 1
}
run show for 5