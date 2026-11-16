import PlattAssemblyKernel
import PlattCertificates.Count131072.C067520
import PlattCertificates.Count131072.C067521
import PlattCertificates.Count131072.C067522
import PlattCertificates.Count131072.C067523
import PlattCertificates.Count131072.C067524
import PlattCertificates.Count131072.C067525
import PlattCertificates.Count131072.C067526
import PlattCertificates.Count131072.C067527
import PlattCertificates.Count131072.C067528
import PlattCertificates.Count131072.C067529
import PlattCertificates.Count131072.C067530
import PlattCertificates.Count131072.C067531
import PlattCertificates.Count131072.C067532
import PlattCertificates.Count131072.C067533
import PlattCertificates.Count131072.C067534
import PlattCertificates.Count131072.C067535
import PlattCertificates.Count131072.C067536
import PlattCertificates.Count131072.C067537
import PlattCertificates.Count131072.C067538
import PlattCertificates.Count131072.C067539
import PlattCertificates.Count131072.C067540
import PlattCertificates.Count131072.C067541
import PlattCertificates.Count131072.C067542
import PlattCertificates.Count131072.C067543
import PlattCertificates.Count131072.C067544
import PlattCertificates.Count131072.C067545
import PlattCertificates.Count131072.C067546
import PlattCertificates.Count131072.C067547
import PlattCertificates.Count131072.C067548
import PlattCertificates.Count131072.C067549
import PlattCertificates.Count131072.C067550
import PlattCertificates.Count131072.C067551
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000235
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67520 : List PrefixCut := [⟨61,171988177,171988279⟩,
⟨64,180349093,180349200⟩]
theorem checked67520 : checkPrefixCuts (2^48) 8853913601 10 Manual.Count131072.C067520.packed 64 cuts67520 = true := by
 decide +kernel
def pointBounds67520 : List (Nat × Nat × Nat) := [(8854038528,115371198302941,115371587548695)]
theorem point_links_checked67520 : (cuts67520.take 1).map (fun c => (8853913601-1+2*2^10*c.k,115371026314764+c.lower,115371415560416+c.upper)) = pointBounds67520 := by
 decide +kernel
def cuts67521 : List PrefixCut := [⟨64,181681606,181681717⟩]
theorem checked67521 : checkPrefixCuts (2^48) 8854044673 10 Manual.Count131072.C067521.packed 64 cuts67521 = true := by
 decide +kernel
def cuts67522 : List PrefixCut := [⟨64,182441871,182441973⟩]
theorem checked67522 : checkPrefixCuts (2^48) 8854175745 10 Manual.Count131072.C067522.packed 64 cuts67522 = true := by
 decide +kernel
def cuts67523 : List PrefixCut := [⟨5,14241734,14241742⟩,
⟨64,181994124,181994232⟩]
theorem checked67523 : checkPrefixCuts (2^48) 8854306817 10 Manual.Count131072.C067523.packed 64 cuts67523 = true := by
 decide +kernel
def pointBounds67523 : List (Nat × Nat × Nat) := [(8854317056,115371585029068,115371974275048)]
theorem point_links_checked67523 : (cuts67523.take 1).map (fun c => (8854306817-1+2*2^10*c.k,115371570787334+c.lower,115371960033306+c.upper)) = pointBounds67523 := by
 decide +kernel
def cuts67524 : List PrefixCut := [⟨64,179098647,179098753⟩]
theorem checked67524 : checkPrefixCuts (2^48) 8854437889 10 Manual.Count131072.C067524.packed 64 cuts67524 = true := by
 decide +kernel
def cuts67525 : List PrefixCut := [⟨13,37129103,37129119⟩,
⟨64,184213927,184214029⟩]
theorem checked67525 : checkPrefixCuts (2^48) 8854568961 10 Manual.Count131072.C067525.packed 64 cuts67525 = true := by
 decide +kernel
def pointBounds67525 : List (Nat × Nat × Nat) := [(8854595584,115371969009208,115372358255410)]
theorem point_links_checked67525 : (cuts67525.take 1).map (fun c => (8854568961-1+2*2^10*c.k,115371931880105+c.lower,115372321126291+c.upper)) = pointBounds67525 := by
 decide +kernel
def cuts67526 : List PrefixCut := [⟨64,181223148,181223248⟩]
theorem checked67526 : checkPrefixCuts (2^48) 8854700033 10 Manual.Count131072.C067526.packed 64 cuts67526 = true := by
 decide +kernel
def cuts67527 : List PrefixCut := [⟨21,59697198,59697231⟩,
⟨64,180775435,180775537⟩]
theorem checked67527 : checkPrefixCuts (2^48) 8854831105 10 Manual.Count131072.C067527.packed 64 cuts67527 = true := by
 decide +kernel
def pointBounds67527 : List (Nat × Nat × Nat) := [(8854874112,115372357014378,115372746260799)]
theorem point_links_checked67527 : (cuts67527.take 1).map (fun c => (8854831105-1+2*2^10*c.k,115372297317180+c.lower,115372686563568+c.upper)) = pointBounds67527 := by
 decide +kernel
def cuts67528 : List PrefixCut := [⟨64,182552821,182552927⟩]
theorem checked67528 : checkPrefixCuts (2^48) 8854962177 10 Manual.Count131072.C067528.packed 64 cuts67528 = true := by
 decide +kernel
def cuts67529 : List PrefixCut := [⟨29,82645353,82645398⟩,
⟨64,184584458,184584563⟩]
theorem checked67529 : checkPrefixCuts (2^48) 8855093249 10 Manual.Count131072.C067529.packed 64 cuts67529 = true := by
 decide +kernel
def pointBounds67529 : List (Nat × Nat × Nat) := [(8855152640,115372743290789,115373132537430)]
theorem point_links_checked67529 : (cuts67529.take 1).map (fun c => (8855093249-1+2*2^10*c.k,115372660645436+c.lower,115373049892032+c.upper)) = pointBounds67529 := by
 decide +kernel
def cuts67530 : List PrefixCut := [⟨64,182738136,182738244⟩]
theorem checked67530 : checkPrefixCuts (2^48) 8855224321 10 Manual.Count131072.C067530.packed 64 cuts67530 = true := by
 decide +kernel
def cuts67531 : List PrefixCut := [⟨37,107499239,107499304⟩,
⟨64,183402933,183403044⟩]
theorem checked67531 : checkPrefixCuts (2^48) 8855355393 10 Manual.Count131072.C067531.packed 64 cuts67531 = true := by
 decide +kernel
def pointBounds67531 : List (Nat × Nat × Nat) := [(8855431168,115373135467269,115373524714143)]
theorem point_links_checked67531 : (cuts67531.take 1).map (fun c => (8855355393-1+2*2^10*c.k,115373027968030+c.lower,115373417214839+c.upper)) = pointBounds67531 := by
 decide +kernel
def cuts67532 : List PrefixCut := [⟨64,177710681,177710782⟩]
theorem checked67532 : checkPrefixCuts (2^48) 8855486465 10 Manual.Count131072.C067532.packed 64 cuts67532 = true := by
 decide +kernel
def cuts67533 : List PrefixCut := [⟨45,127742836,127742908⟩,
⟨64,180791162,180791264⟩]
theorem checked67533 : checkPrefixCuts (2^48) 8855617537 10 Manual.Count131072.C067533.packed 64 cuts67533 = true := by
 decide +kernel
def pointBounds67533 : List (Nat × Nat × Nat) := [(8855709696,115373516824480,115373906071573)]
theorem point_links_checked67533 : (cuts67533.take 1).map (fun c => (8855617537-1+2*2^10*c.k,115373389081644+c.lower,115373778328665+c.upper)) = pointBounds67533 := by
 decide +kernel
def cuts67534 : List PrefixCut := [⟨64,181297038,181297145⟩]
theorem checked67534 : checkPrefixCuts (2^48) 8855748609 10 Manual.Count131072.C067534.packed 64 cuts67534 = true := by
 decide +kernel
def cuts67535 : List PrefixCut := [⟨53,151958163,151958246⟩,
⟨64,182343215,182343314⟩]
theorem checked67535 : checkPrefixCuts (2^48) 8855879681 10 Manual.Count131072.C067535.packed 64 cuts67535 = true := by
 decide +kernel
def pointBounds67535 : List (Nat × Nat × Nat) := [(8855988224,115373903128007,115374292375320)]
theorem point_links_checked67535 : (cuts67535.take 1).map (fun c => (8855879681-1+2*2^10*c.k,115373751169844+c.lower,115374140417074+c.upper)) = pointBounds67535 := by
 decide +kernel
def cuts67536 : List PrefixCut := [⟨64,182308732,182308842⟩]
theorem checked67536 : checkPrefixCuts (2^48) 8856010753 10 Manual.Count131072.C067536.packed 64 cuts67536 = true := by
 decide +kernel
def cuts67537 : List PrefixCut := [⟨61,172612334,172612442⟩,
⟨64,180971146,180971259⟩]
theorem checked67537 : checkPrefixCuts (2^48) 8856141825 10 Manual.Count131072.C067537.packed 64 cuts67537 = true := by
 decide +kernel
def pointBounds67537 : List (Nat × Nat × Nat) := [(8856266752,115374288434125,115374677681672)]
theorem point_links_checked67537 : (cuts67537.take 1).map (fun c => (8856141825-1+2*2^10*c.k,115374115821791+c.lower,115374505069230+c.upper)) = pointBounds67537 := by
 decide +kernel
def cuts67538 : List PrefixCut := [⟨64,183574624,183574737⟩]
theorem checked67538 : checkPrefixCuts (2^48) 8856272897 10 Manual.Count131072.C067538.packed 64 cuts67538 = true := by
 decide +kernel
def cuts67539 : List PrefixCut := [⟨64,179630963,179631066⟩]
theorem checked67539 : checkPrefixCuts (2^48) 8856403969 10 Manual.Count131072.C067539.packed 64 cuts67539 = true := by
 decide +kernel
def cuts67540 : List PrefixCut := [⟨5,13666082,13666090⟩,
⟨64,181090236,181090333⟩]
theorem checked67540 : checkPrefixCuts (2^48) 8856535041 10 Manual.Count131072.C067540.packed 64 cuts67540 = true := by
 decide +kernel
def pointBounds67540 : List (Nat × Nat × Nat) := [(8856545280,115374673664606,115375062912382)]
theorem point_links_checked67540 : (cuts67540.take 1).map (fun c => (8856535041-1+2*2^10*c.k,115374659998524+c.lower,115375049246292+c.upper)) = pointBounds67540 := by
 decide +kernel
def cuts67541 : List PrefixCut := [⟨64,183502911,183503019⟩]
theorem checked67541 : checkPrefixCuts (2^48) 8856666113 10 Manual.Count131072.C067541.packed 64 cuts67541 = true := by
 decide +kernel
def cuts67542 : List PrefixCut := [⟨13,37946055,37946078⟩,
⟨64,180862428,180862537⟩]
theorem checked67542 : checkPrefixCuts (2^48) 8856797185 10 Manual.Count131072.C067542.packed 64 cuts67542 = true := by
 decide +kernel
def pointBounds67542 : List (Nat × Nat × Nat) := [(8856823808,115375062537726,115375451785722)]
theorem point_links_checked67542 : (cuts67542.take 1).map (fun c => (8856797185-1+2*2^10*c.k,115375024591671+c.lower,115375413839644+c.upper)) = pointBounds67542 := by
 decide +kernel
def cuts67543 : List PrefixCut := [⟨64,180827968,180828077⟩]
theorem checked67543 : checkPrefixCuts (2^48) 8856928257 10 Manual.Count131072.C067543.packed 64 cuts67543 = true := by
 decide +kernel
def cuts67544 : List PrefixCut := [⟨21,61048699,61048734⟩,
⟨64,183240540,183240641⟩]
theorem checked67544 : checkPrefixCuts (2^48) 8857059329 10 Manual.Count131072.C067544.packed 64 cuts67544 = true := by
 decide +kernel
def pointBounds67544 : List (Nat × Nat × Nat) := [(8857102336,115375447330766,115375836578992)]
theorem point_links_checked67544 : (cuts67544.take 1).map (fun c => (8857059329-1+2*2^10*c.k,115375386282067+c.lower,115375775530258+c.upper)) = pointBounds67544 := by
 decide +kernel
def cuts67545 : List PrefixCut := [⟨64,182761124,182761232⟩]
theorem checked67545 : checkPrefixCuts (2^48) 8857190401 10 Manual.Count131072.C067545.packed 64 cuts67545 = true := by
 decide +kernel
def cuts67546 : List PrefixCut := [⟨29,80304714,80304762⟩,
⟨64,179262776,179262884⟩]
theorem checked67546 : checkPrefixCuts (2^48) 8857321473 10 Manual.Count131072.C067546.packed 64 cuts67546 = true := by
 decide +kernel
def pointBounds67546 : List (Nat × Nat × Nat) := [(8857380864,115375832588445,115376221836893)]
theorem point_links_checked67546 : (cuts67546.take 1).map (fun c => (8857321473-1+2*2^10*c.k,115375752283731+c.lower,115376141532131+c.upper)) = pointBounds67546 := by
 decide +kernel
def cuts67547 : List PrefixCut := [⟨64,180118146,180118258⟩]
theorem checked67547 : checkPrefixCuts (2^48) 8857452545 10 Manual.Count131072.C067547.packed 64 cuts67547 = true := by
 decide +kernel
def cuts67548 : List PrefixCut := [⟨37,106550650,106550710⟩,
⟨64,182022146,182022249⟩]
theorem checked67548 : checkPrefixCuts (2^48) 8857583617 10 Manual.Count131072.C067548.packed 64 cuts67548 = true := by
 decide +kernel
def pointBounds67548 : List (Nat × Nat × Nat) := [(8857659392,115376218215303,115376607463983)]
theorem point_links_checked67548 : (cuts67548.take 1).map (fun c => (8857583617-1+2*2^10*c.k,115376111664653+c.lower,115376500913273+c.upper)) = pointBounds67548 := by
 decide +kernel
def cuts67549 : List PrefixCut := [⟨64,183608294,183608407⟩]
theorem checked67549 : checkPrefixCuts (2^48) 8857714689 10 Manual.Count131072.C067549.packed 64 cuts67549 = true := by
 decide +kernel
def cuts67550 : List PrefixCut := [⟨45,127615374,127615452⟩,
⟨64,181921417,181921523⟩]
theorem checked67550 : checkPrefixCuts (2^48) 8857845761 10 Manual.Count131072.C067550.packed 64 cuts67550 = true := by
 decide +kernel
def pointBounds67550 : List (Nat × Nat × Nat) := [(8857937920,115376604910467,115376994159381)]
theorem point_links_checked67550 : (cuts67550.take 1).map (fun c => (8857845761-1+2*2^10*c.k,115376477295093+c.lower,115376866543929+c.upper)) = pointBounds67550 := by
 decide +kernel
def cuts67551 : List PrefixCut := [⟨64,183412204,183412316⟩]
theorem checked67551 : checkPrefixCuts (2^48) 8857976833 10 Manual.Count131072.C067551.packed 64 cuts67551 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000235
