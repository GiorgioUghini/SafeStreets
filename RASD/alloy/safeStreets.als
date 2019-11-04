/******DOMAIN ASSUMPTIONS******/
sig Email {} {one u: Customer | this = u.email}
sig Password {} {some u: Customer | this = u.password}

abstract sig Customer{
    email: one Email,
    password: one Password
}

sig User extends Customer {
    reports: set Violation
}
sig Officer extends Customer{}

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
}
sig AccidentType {} { 
    //an accidentType must belong to an accident
    some a: Accident | this in a.accidentType
}

fun getLicensePlate[v: Violation] : one LicensePlate {
    let x = {p: Picture | p in v.pictures and #p.licensePlate=1} |
        x.licensePlate
}

//a violation must have exactly one license plate
fact {
    //at least one
    all v: Violation | some p:Picture | p in v.pictures and #(p.licensePlate)=1
    //at most one
    all v: Violation | no disj p1, p2: Picture |
        (p1 in v.pictures) and (p2 in v.pictures) and (p1.licensePlate != p2.licensePlate)
}

/******************ASSERTIONS******************/

//a report cannot belong to 2 users
check {
    no disj u1, u2: User | some v: Violation | v in u1.reports and v in u2.reports
} for 5

//2 users cannot have same email
check {
    no disj c1, c2: Customer | c1.email = c2.email
} for 5

pred show{
    #User = 2
    all u: User | #u.reports > 0
    #Violation > 0
    all v: Violation | #(v.pictures) > 1
    all p: Picture | #p.licensePlate = 1
}
run show for 5