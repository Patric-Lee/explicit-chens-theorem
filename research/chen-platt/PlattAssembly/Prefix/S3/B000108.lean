import PlattAssemblyKernel
import PlattCertificates.Count131072.C023456
import PlattCertificates.Count131072.C023457
import PlattCertificates.Count131072.C023458
import PlattCertificates.Count131072.C023459
import PlattCertificates.Count131072.C023460
import PlattCertificates.Count131072.C023461
import PlattCertificates.Count131072.C023462
import PlattCertificates.Count131072.C023463
import PlattCertificates.Count131072.C023464
import PlattCertificates.Count131072.C023465
import PlattCertificates.Count131072.C023466
import PlattCertificates.Count131072.C023467
import PlattCertificates.Count131072.C023468
import PlattCertificates.Count131072.C023469
import PlattCertificates.Count131072.C023470
import PlattCertificates.Count131072.C023471
import PlattCertificates.Count131072.C023472
import PlattCertificates.Count131072.C023473
import PlattCertificates.Count131072.C023474
import PlattCertificates.Count131072.C023475
import PlattCertificates.Count131072.C023476
import PlattCertificates.Count131072.C023477
import PlattCertificates.Count131072.C023478
import PlattCertificates.Count131072.C023479
import PlattCertificates.Count131072.C023480
import PlattCertificates.Count131072.C023481
import PlattCertificates.Count131072.C023482
import PlattCertificates.Count131072.C023483
import PlattCertificates.Count131072.C023484
import PlattCertificates.Count131072.C023485
import PlattCertificates.Count131072.C023486
import PlattCertificates.Count131072.C023487
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000108
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts23456 : List PrefixCut := [⟨54,234167356,234167490⟩,
⟨128,546871515,546871825⟩]
theorem checked23456 : checkPrefixCuts (2^48) 3078356993 9 Manual.Count131072.C023456.packed 128 cuts23456 = true := by
 decide +kernel
def pointBounds23456 : List (Nat × Nat × Nat) := [(3078412288,102079232670565,102079614225355)]
theorem point_links_checked23456 : (cuts23456.take 1).map (fun c => (3078356993-1+2*2^9*c.k,102078998503209+c.lower,102079380057865+c.upper)) = pointBounds23456 := by
 decide +kernel
def cuts23457 : List PrefixCut := [⟨20,85306554,85306604⟩,
⟨114,493362123,493362411⟩,
⟨128,554345374,554345694⟩]
theorem checked23457 : checkPrefixCuts (2^48) 3078488065 9 Manual.Count131072.C023457.packed 128 cuts23457 = true := by
 decide +kernel
def pointBounds23457 : List (Nat × Nat × Nat) := [(3078508544,102079630681278,102080012236294),(3078604800,102080038736847,102080420292101)]
theorem point_links_checked23457 : (cuts23457.take 2).map (fun c => (3078488065-1+2*2^9*c.k,102079545374724+c.lower,102079926929690+c.upper)) = pointBounds23457 := by
 decide +kernel
def cuts23458 : List PrefixCut := [⟨80,343585405,343585590⟩,
⟨128,549293402,549293704⟩]
theorem checked23458 : checkPrefixCuts (2^48) 3078619137 9 Manual.Count131072.C023458.packed 128 cuts23458 = true := by
 decide +kernel
def pointBounds23458 : List (Nat × Nat × Nat) := [(3078701056,102080443305503,102080824860974)]
theorem point_links_checked23458 : (cuts23458.take 1).map (fun c => (3078619137-1+2*2^9*c.k,102080099720098+c.lower,102080481275384+c.upper)) = pointBounds23458 := by
 decide +kernel
def cuts23459 : List PrefixCut := [⟨46,193545379,193545485⟩,
⟨128,547441521,547441827⟩]
theorem checked23459 : checkPrefixCuts (2^48) 3078750209 9 Manual.Count131072.C023459.packed 128 cuts23459 = true := by
 decide +kernel
def pointBounds23459 : List (Nat × Nat × Nat) := [(3078797312,102080842558879,102081224114573)]
theorem point_links_checked23459 : (cuts23459.take 1).map (fun c => (3078750209-1+2*2^9*c.k,102080649013500+c.lower,102081030569088+c.upper)) = pointBounds23459 := by
 decide +kernel
def cuts23460 : List PrefixCut := [⟨12,50738639,50738667⟩,
⟨106,450332683,450332939⟩,
⟨128,546595414,546595724⟩]
theorem checked23460 : checkPrefixCuts (2^48) 3078881281 9 Manual.Count131072.C023460.packed 128 cuts23460 = true := by
 decide +kernel
def pointBounds23460 : List (Nat × Nat × Nat) := [(3078893568,102081247193660,102081628749582),(3078989824,102081646787704,102082028343854)]
theorem point_links_checked23460 : (cuts23460.take 2).map (fun c => (3078881281-1+2*2^9*c.k,102081196455021+c.lower,102081578010915+c.upper)) = pointBounds23460 := by
 decide +kernel
def cuts23461 : List PrefixCut := [⟨72,298930892,298931067⟩,
⟨128,537156369,537156681⟩]
theorem checked23461 : checkPrefixCuts (2^48) 3079012353 9 Manual.Count131072.C023461.packed 128 cuts23461 = true := by
 decide +kernel
def pointBounds23461 : List (Nat × Nat × Nat) := [(3079086080,102082041981327,102082423537706)]
theorem point_links_checked23461 : (cuts23461.take 1).map (fun c => (3079012353-1+2*2^9*c.k,102081743050435+c.lower,102082124606639+c.upper)) = pointBounds23461 := by
 decide +kernel
def cuts23462 : List PrefixCut := [⟨38,163720325,163720414⟩,
⟨128,556695595,556695903⟩]
theorem checked23462 : checkPrefixCuts (2^48) 3079143425 9 Manual.Count131072.C023462.packed 128 cuts23462 = true := by
 decide +kernel
def pointBounds23462 : List (Nat × Nat × Nat) := [(3079182336,102082443927129,102082825483734)]
theorem point_links_checked23462 : (cuts23462.take 1).map (fun c => (3079143425-1+2*2^9*c.k,102082280206804+c.lower,102082661763320+c.upper)) = pointBounds23462 := by
 decide +kernel
def cuts23463 : List PrefixCut := [⟨4,17184972,17184981⟩,
⟨98,418922860,418923099⟩,
⟨128,547988209,547988520⟩]
theorem checked23463 : checkPrefixCuts (2^48) 3079274497 9 Manual.Count131072.C023463.packed 128 cuts23463 = true := by
 decide +kernel
def pointBounds23463 : List (Nat × Nat × Nat) := [(3079278592,102082854087371,102083235644204),(3079374848,102083255825259,102083637382322)]
theorem point_links_checked23463 : (cuts23463.take 2).map (fun c => (3079274497-1+2*2^9*c.k,102082836902399+c.lower,102083218459223+c.upper)) = pointBounds23463 := by
 decide +kernel
def cuts23464 : List PrefixCut := [⟨64,276498983,276499132⟩,
⟨128,554088903,554089208⟩]
theorem checked23464 : checkPrefixCuts (2^48) 3079405569 9 Manual.Count131072.C023464.packed 128 cuts23464 = true := by
 decide +kernel
def pointBounds23464 : List (Nat × Nat × Nat) := [(3079471104,102083661389591,102084042946875)]
theorem point_links_checked23464 : (cuts23464.take 1).map (fun c => (3079405569-1+2*2^9*c.k,102083384890608+c.lower,102083766447743+c.upper)) = pointBounds23464 := by
 decide +kernel
def cuts23465 : List PrefixCut := [⟨30,126590722,126590793⟩,
⟨124,524909197,524909497⟩,
⟨128,542640385,542640694⟩]
theorem checked23465 : checkPrefixCuts (2^48) 3079536641 9 Manual.Count131072.C023465.packed 128 cuts23465 = true := by
 decide +kernel
def pointBounds23465 : List (Nat × Nat × Nat) := [(3079567360,102084065570233,102084447127744),(3079663616,102084463888708,102084845446448)]
theorem point_links_checked23465 : (cuts23465.take 2).map (fun c => (3079536641-1+2*2^9*c.k,102083938979511+c.lower,102084320536951+c.upper)) = pointBounds23465 := by
 decide +kernel
def cuts23466 : List PrefixCut := [⟨90,382951147,382951367⟩,
⟨128,546547312,546547621⟩]
theorem checked23466 : checkPrefixCuts (2^48) 3079667713 9 Manual.Count131072.C023466.packed 128 cuts23466 = true := by
 decide +kernel
def pointBounds23466 : List (Nat × Nat × Nat) := [(3079759872,102084864571043,102085246129012)]
theorem point_links_checked23466 : (cuts23466.take 1).map (fun c => (3079667713-1+2*2^9*c.k,102084481619896+c.lower,102084863177645+c.upper)) = pointBounds23466 := by
 decide +kernel
def cuts23467 : List PrefixCut := [⟨56,240363761,240363897⟩,
⟨128,547986328,547986628⟩]
theorem checked23467 : checkPrefixCuts (2^48) 3079798785 9 Manual.Count131072.C023467.packed 128 cuts23467 = true := by
 decide +kernel
def pointBounds23467 : List (Nat × Nat × Nat) := [(3079856128,102085268530969,102085650089163)]
theorem point_links_checked23467 : (cuts23467.take 1).map (fun c => (3079798785-1+2*2^9*c.k,102085028167208+c.lower,102085409725266+c.upper)) = pointBounds23467 := by
 decide +kernel
def cuts23468 : List PrefixCut := [⟨22,96416133,96416189⟩,
⟨116,505285731,505286029⟩,
⟨128,554908509,554908835⟩]
theorem checked23468 : checkPrefixCuts (2^48) 3079929857 9 Manual.Count131072.C023468.packed 128 cuts23468 = true := by
 decide +kernel
def pointBounds23468 : List (Nat × Nat × Nat) := [(3079952384,102085672569669,102086054128083),(3080048640,102086081439267,102086462997923)]
theorem point_links_checked23468 : (cuts23468.take 2).map (fun c => (3079929857-1+2*2^9*c.k,102085576153536+c.lower,102085957711894+c.upper)) = pointBounds23468 := by
 decide +kernel
def cuts23469 : List PrefixCut := [⟨82,354025132,354025335⟩,
⟨128,551229550,551229862⟩]
theorem checked23469 : checkPrefixCuts (2^48) 3080060929 9 Manual.Count131072.C023469.packed 128 cuts23469 = true := by
 decide +kernel
def pointBounds23469 : List (Nat × Nat × Nat) := [(3080144896,102086485087177,102086866646064)]
theorem point_links_checked23469 : (cuts23469.take 1).map (fun c => (3080060929-1+2*2^9*c.k,102086131062045+c.lower,102086512620729+c.upper)) = pointBounds23469 := by
 decide +kernel
def cuts23470 : List PrefixCut := [⟨48,200673832,200673945⟩,
⟨128,545723114,545723424⟩]
theorem checked23470 : checkPrefixCuts (2^48) 3080192001 9 Manual.Count131072.C023470.packed 128 cuts23470 = true := by
 decide +kernel
def pointBounds23470 : List (Nat × Nat × Nat) := [(3080241152,102086882965427,102087264524536)]
theorem point_links_checked23470 : (cuts23470.take 1).map (fun c => (3080192001-1+2*2^9*c.k,102086682291595+c.lower,102087063850591+c.upper)) = pointBounds23470 := by
 decide +kernel
def cuts23471 : List PrefixCut := [⟨15,63325049,63325085⟩,
⟨110,470955476,470955735⟩,
⟨128,549446390,549446698⟩]
theorem checked23471 : checkPrefixCuts (2^48) 3080323073 9 Manual.Count131072.C023471.packed 128 cuts23471 = true := by
 decide +kernel
def pointBounds23471 : List (Nat × Nat × Nat) := [(3080338432,102087291339758,102087672899100),(3080435712,102087698970185,102088080529750)]
theorem point_links_checked23471 : (cuts23471.take 2).map (fun c => (3080323073-1+2*2^9*c.k,102087228014709+c.lower,102087609574015+c.upper)) = pointBounds23471 := by
 decide +kernel
def cuts23472 : List PrefixCut := [⟨77,326842314,326842500⟩,
⟨128,549879818,549880129⟩]
theorem checked23472 : checkPrefixCuts (2^48) 3080454145 9 Manual.Count131072.C023472.packed 128 cuts23472 = true := by
 decide +kernel
def pointBounds23472 : List (Nat × Nat × Nat) := [(3080532992,102088104303413,102088485863213)]
theorem point_links_checked23472 : (cuts23472.take 1).map (fun c => (3080454145-1+2*2^9*c.k,102087777461099+c.lower,102088159020713+c.upper)) = pointBounds23472 := by
 decide +kernel
def cuts23473 : List PrefixCut := [⟨44,186303266,186303375⟩,
⟨128,546201773,546202088⟩]
theorem checked23473 : checkPrefixCuts (2^48) 3080585217 9 Manual.Count131072.C023473.packed 128 cuts23473 = true := by
 decide +kernel
def pointBounds23473 : List (Nat × Nat × Nat) := [(3080630272,102088513644183,102088895204217)]
theorem point_links_checked23473 : (cuts23473.take 1).map (fun c => (3080585217-1+2*2^9*c.k,102088327340917+c.lower,102088708900842+c.upper)) = pointBounds23473 := by
 decide +kernel
def cuts23474 : List PrefixCut := [⟨11,48058800,48058825⟩,
⟨106,447140811,447141063⟩,
⟨128,541793043,541793346⟩]
theorem checked23474 : checkPrefixCuts (2^48) 3080716289 9 Manual.Count131072.C023474.packed 128 cuts23474 = true := by
 decide +kernel
def pointBounds23474 : List (Nat × Nat × Nat) := [(3080727552,102088921601490,102089303161755),(3080824832,102089320683501,102089702243993)]
theorem point_links_checked23474 : (cuts23474.take 2).map (fun c => (3080716289-1+2*2^9*c.k,102088873542690+c.lower,102089255102930+c.upper)) = pointBounds23474 := by
 decide +kernel
def cuts23475 : List PrefixCut := [⟨73,314101564,314101744⟩,
⟨128,554651817,554652130⟩]
theorem checked23475 : checkPrefixCuts (2^48) 3080847361 9 Manual.Count131072.C023475.packed 128 cuts23475 = true := by
 decide +kernel
def pointBounds23475 : List (Nat × Nat × Nat) := [(3080922112,102089729437297,102090110998020)]
theorem point_links_checked23475 : (cuts23475.take 1).map (fun c => (3080847361-1+2*2^9*c.k,102089415335733+c.lower,102089796896276+c.upper)) = pointBounds23475 := by
 decide +kernel
def cuts23476 : List PrefixCut := [⟨40,167642538,167642634⟩,
⟨128,543482722,543483030⟩]
theorem checked23476 : checkPrefixCuts (2^48) 3080978433 9 Manual.Count131072.C023476.packed 128 cuts23476 = true := by
 decide +kernel
def pointBounds23476 : List (Nat × Nat × Nat) := [(3081019392,102090137630088,102090519191040)]
theorem point_links_checked23476 : (cuts23476.take 1).map (fun c => (3080978433-1+2*2^9*c.k,102089969987550+c.lower,102090351548406+c.upper)) = pointBounds23476 := by
 decide +kernel
def cuts23477 : List PrefixCut := [⟨7,29690354,29690372⟩,
⟨102,434020448,434020694⟩,
⟨128,544464474,544464785⟩]
theorem checked23477 : checkPrefixCuts (2^48) 3081109505 9 Manual.Count131072.C023477.packed 128 cuts23477 = true := by
 decide +kernel
def pointBounds23477 : List (Nat × Nat × Nat) := [(3081116672,102090543160626,102090924721808),(3081213952,102090947490720,102091329052130)]
theorem point_links_checked23477 : (cuts23477.take 2).map (fun c => (3081109505-1+2*2^9*c.k,102090513470272+c.lower,102090895031436+c.upper)) = pointBounds23477 := by
 decide +kernel
def cuts23478 : List PrefixCut := [⟨69,298806212,298806379⟩,
⟨128,550013650,550013964⟩]
theorem checked23478 : checkPrefixCuts (2^48) 3081240577 9 Manual.Count131072.C023478.packed 128 cuts23478 = true := by
 decide +kernel
def pointBounds23478 : List (Nat × Nat × Nat) := [(3081311232,102091356740958,102091738302600)]
theorem point_links_checked23478 : (cuts23478.take 1).map (fun c => (3081240577-1+2*2^9*c.k,102091057934746+c.lower,102091439496221+c.upper)) = pointBounds23478 := by
 decide +kernel
def cuts23479 : List PrefixCut := [⟨36,152731728,152731810⟩,
⟨128,545605598,545605904⟩]
theorem checked23479 : checkPrefixCuts (2^48) 3081371649 9 Manual.Count131072.C023479.packed 128 cuts23479 = true := by
 decide +kernel
def pointBounds23479 : List (Nat × Nat × Nat) := [(3081408512,102091760680124,102092142241995)]
theorem point_links_checked23479 : (cuts23479.take 1).map (fun c => (3081371649-1+2*2^9*c.k,102091607948396+c.lower,102091989510185+c.upper)) = pointBounds23479 := by
 decide +kernel
def cuts23480 : List PrefixCut := [⟨3,12240007,12240015⟩,
⟨98,422182317,422182548⟩,
⟨128,554168564,554168868⟩]
theorem checked23480 : checkPrefixCuts (2^48) 3081502721 9 Manual.Count131072.C023480.packed 128 cuts23480 = true := by
 decide +kernel
def pointBounds23480 : List (Nat × Nat × Nat) := [(3081505792,102092165794001,102092547356104),(3081603072,102092575736311,102092957298637)]
theorem point_links_checked23480 : (cuts23480.take 2).map (fun c => (3081502721-1+2*2^9*c.k,102092153553994+c.lower,102092535116089+c.upper)) = pointBounds23480 := by
 decide +kernel
def cuts23481 : List PrefixCut := [⟨65,279313161,279313324⟩,
⟨128,546015944,546016253⟩]
theorem checked23481 : checkPrefixCuts (2^48) 3081633793 9 Manual.Count131072.C023481.packed 128 cuts23481 = true := by
 decide +kernel
def pointBounds23481 : List (Nat × Nat × Nat) := [(3081700352,102092987035719,102093368598281)]
theorem point_links_checked23481 : (cuts23481.take 1).map (fun c => (3081633793-1+2*2^9*c.k,102092707722558+c.lower,102093089284957+c.upper)) = pointBounds23481 := by
 decide +kernel
def cuts23482 : List PrefixCut := [⟨32,137368033,137368108⟩,
⟨127,544074784,544075086⟩,
⟨128,548002049,548002353⟩]
theorem checked23482 : checkPrefixCuts (2^48) 3081764865 9 Manual.Count131072.C023482.packed 128 cuts23482 = true := by
 decide +kernel
def pointBounds23482 : List (Nat × Nat × Nat) := [(3081797632,102093391106535,102093772669318),(3081894912,102093797813286,102094179376296)]
theorem point_links_checked23482 : (cuts23482.take 2).map (fun c => (3081764865-1+2*2^9*c.k,102093253738502+c.lower,102093635301210+c.upper)) = pointBounds23482 := by
 decide +kernel
def cuts23483 : List PrefixCut := [⟨94,400300704,400300934⟩,
⟨128,535832007,535832318⟩]
theorem checked23483 : checkPrefixCuts (2^48) 3081895937 9 Manual.Count131072.C023483.packed 128 cuts23483 = true := by
 decide +kernel
def pointBounds23483 : List (Nat × Nat × Nat) := [(3081992192,102094202041255,102094583604497)]
theorem point_links_checked23483 : (cuts23483.take 1).map (fun c => (3081895937-1+2*2^9*c.k,102093801740551+c.lower,102094183303563+c.upper)) = pointBounds23483 := by
 decide +kernel
def cuts23484 : List PrefixCut := [⟨61,262473573,262473726⟩,
⟨128,545124392,545124713⟩]
theorem checked23484 : checkPrefixCuts (2^48) 3082027009 9 Manual.Count131072.C023484.packed 128 cuts23484 = true := by
 decide +kernel
def pointBounds23484 : List (Nat × Nat × Nat) := [(3082089472,102094600046131,102094981609607)]
theorem point_links_checked23484 : (cuts23484.take 1).map (fun c => (3082027009-1+2*2^9*c.k,102094337572558+c.lower,102094719135881+c.upper)) = pointBounds23484 := by
 decide +kernel
def cuts23485 : List PrefixCut := [⟨28,119542501,119542571⟩,
⟨123,534051600,534051900⟩,
⟨128,555694477,555694789⟩]
theorem checked23485 : checkPrefixCuts (2^48) 3082158081 9 Manual.Count131072.C023485.packed 128 cuts23485 = true := by
 decide +kernel
def pointBounds23485 : List (Nat × Nat × Nat) := [(3082186752,102095002239451,102095383803165),(3082284032,102095416748550,102095798312494)]
theorem point_links_checked23485 : (cuts23485.take 2).map (fun c => (3082158081-1+2*2^9*c.k,102094882696950+c.lower,102095264260594+c.upper)) = pointBounds23485 := by
 decide +kernel
def cuts23486 : List PrefixCut := [⟨90,387191269,387191487⟩,
⟨128,547817469,547817777⟩]
theorem checked23486 : checkPrefixCuts (2^48) 3082289153 9 Manual.Count131072.C023486.packed 128 cuts23486 = true := by
 decide +kernel
def pointBounds23486 : List (Nat × Nat × Nat) := [(3082381312,102095825582696,102096207146870)]
theorem point_links_checked23486 : (cuts23486.take 1).map (fun c => (3082289153-1+2*2^9*c.k,102095438391427+c.lower,102095819955383+c.upper)) = pointBounds23486 := by
 decide +kernel
def cuts23487 : List PrefixCut := [⟨57,241163771,241163904⟩,
⟨128,551081395,551081703⟩]
theorem checked23487 : checkPrefixCuts (2^48) 3082420225 9 Manual.Count131072.C023487.packed 128 cuts23487 = true := by
 decide +kernel
def pointBounds23487 : List (Nat × Nat × Nat) := [(3082478592,102096227372667,102096608937064)]
theorem point_links_checked23487 : (cuts23487.take 1).map (fun c => (3082420225-1+2*2^9*c.k,102095986208896+c.lower,102096367773160+c.upper)) = pointBounds23487 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000108
