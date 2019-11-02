// Domain
sig Email, Password {}
sig Customer{
    email: one Email,
    password: one Password
}
sig LicensePlace {}
sig Position {}
sig ViolationType{}

sig Violation {
    licensePlace: one LicensePlace,
    violationType: one ViolationType,
    position: one Position
}

sig User extends Customer {
    reports: set Violation
}
sig Officer extends Customer{}

//2 users cannot have same email
fact {
    no c1, c2: Customer | c1.email = c2.email
}

//a report cannot belong to 2 users
fact {
    no disj u1, u2: User | one v: Violation | v in u1.reports and v in u2.reports
}

pred show{}
run show for 3