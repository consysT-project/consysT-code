# How to run?

Use `mvn exec:java -Dexec.mainClass=de.tuda.stg.consys.auctions.TestSystemDistributed -Dexec.args=0` and 
`mvn exec:java -Dexec.mainClass=de.tuda.stg.consys.auctions.TestSystemDistributed -Dexec.args=1` 
to start the test.

# What happens?

## Test numbers
1:TestNoWrapper
2:TestStrongWrapper
3:TestWeakToStrong
4:TestCreateBidSubSys
5:TestCreateBidSubSysOnMain

## Test Abfolge
2 Random bid sequenzen (fur die beiden systeme) für alle tests gleich (aus vergleichs gründen)

* System 1:
registriert 2 user (Hans, Peter)
wartet (1Sekunde)
startet auktion
bid sequenz 1
wartet bis auktionszeit (5 sekunden ) rum ist
stoppt auktion
bestimmt gewinner

* System 2:
registriert 2 user + 1 user der dem ersten system gleicht (Alice, Bob, Peter)
wartet auf auktionsstart
bid sequenz 2
wartet auf auktionsende
bestimmt gewinner

* Bids:
    * Sys1: user 1 -> user 2 -> user 1 -> user 2
    * Sys2: user 1 -> user 2 -> user 3 -> user 1 -> user 2 -> user 3