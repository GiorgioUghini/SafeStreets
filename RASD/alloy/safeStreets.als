// Domain assumptions
sig Email {} {one u: User | this = u.email}
sig Password {} {one u: User | this = u.password}

abstract sig Customer{
    email: one Email,
    password: one Password
}
// all tickets, licensePlace and position must belong to a violation
sig Ticket {} { one v: Violation | this = v.ticket }
sig LicensePlate {} { one v: Violation | this = v.licensePlate }
sig Position {} { one v: Violation | this = v.position }

//a violation type can belong to no violation
sig ViolationType{}

sig Violation {
    licensePlate: one LicensePlate,
    violationType: one ViolationType,
    position: one Position,
    ticket: lone Ticket
} {
    //a violation must belong to a user
    one u: User | this in u.reports
}

sig User extends Customer {
    reports: set Violation
}
sig Officer extends Customer{}

//2 users cannot have same email
fact {
    no disj c1, c2: Customer | c1.email = c2.email
}

//a report cannot belong to 2 users
fact {
    no disj u1, u2: User | one v: Violation | v in u1.reports and v in u2.reports
}

pred show{
    #User = 2
    #Violation > 0
}
run show for 5