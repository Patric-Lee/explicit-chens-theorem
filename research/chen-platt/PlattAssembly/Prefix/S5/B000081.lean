import PlattAssemblyKernel
import PlattCertificates.Count131072.C042592
import PlattCertificates.Count131072.C042593
import PlattCertificates.Count131072.C042594
import PlattCertificates.Count131072.C042595
import PlattCertificates.Count131072.C042596
import PlattCertificates.Count131072.C042597
import PlattCertificates.Count131072.C042598
import PlattCertificates.Count131072.C042599
import PlattCertificates.Count131072.C042600
import PlattCertificates.Count131072.C042601
import PlattCertificates.Count131072.C042602
import PlattCertificates.Count131072.C042603
import PlattCertificates.Count131072.C042604
import PlattCertificates.Count131072.C042605
import PlattCertificates.Count131072.C042606
import PlattCertificates.Count131072.C042607
import PlattCertificates.Count131072.C042608
import PlattCertificates.Count131072.C042609
import PlattCertificates.Count131072.C042610
import PlattCertificates.Count131072.C042611
import PlattCertificates.Count131072.C042612
import PlattCertificates.Count131072.C042613
import PlattCertificates.Count131072.C042614
import PlattCertificates.Count131072.C042615
import PlattCertificates.Count131072.C042616
import PlattCertificates.Count131072.C042617
import PlattCertificates.Count131072.C042618
import PlattCertificates.Count131072.C042619
import PlattCertificates.Count131072.C042620
import PlattCertificates.Count131072.C042621
import PlattCertificates.Count131072.C042622
import PlattCertificates.Count131072.C042623
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000081
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42592 : List PrefixCut := [⟨64,294644371,294644545⟩]
theorem checked42592 : checkPrefixCuts (2^48) 5586550785 10 Manual.Count131072.C042592.packed 64 cuts42592 = true := by
 decide +kernel
def cuts42593 : List PrefixCut := [⟨16,70435505,70435544⟩,
⟨64,291664899,291665068⟩]
theorem checked42593 : checkPrefixCuts (2^48) 5586681857 10 Manual.Count131072.C042593.packed 64 cuts42593 = true := by
 decide +kernel
def pointBounds42593 : List (Nat × Nat × Nat) := [(5586714624,109654546012706,109654931982684)]
theorem point_links_checked42593 : (cuts42593.take 1).map (fun c => (5586681857-1+2*2^10*c.k,109654475577201+c.lower,109654861547140+c.upper)) = pointBounds42593 := by
 decide +kernel
def cuts42594 : List PrefixCut := [⟨38,172254909,172255010⟩,
⟨64,290650431,290650602⟩]
theorem checked42594 : checkPrefixCuts (2^48) 5586812929 10 Manual.Count131072.C042594.packed 64 cuts42594 = true := by
 decide +kernel
def pointBounds42594 : List (Nat × Nat × Nat) := [(5586890752,109654939497009,109655325467218)]
theorem point_links_checked42594 : (cuts42594.take 1).map (fun c => (5586812929-1+2*2^10*c.k,109654767242100+c.lower,109655153212208+c.upper)) = pointBounds42594 := by
 decide +kernel
def cuts42595 : List PrefixCut := [⟨60,278451809,278451969⟩,
⟨64,296286218,296286389⟩]
theorem checked42595 : checkPrefixCuts (2^48) 5586944001 10 Manual.Count131072.C042595.packed 64 cuts42595 = true := by
 decide +kernel
def pointBounds42595 : List (Nat × Nat × Nat) := [(5587066880,109655336344340,109655722314779)]
theorem point_links_checked42595 : (cuts42595.take 1).map (fun c => (5586944001-1+2*2^10*c.k,109655057892531+c.lower,109655443862810+c.upper)) = pointBounds42595 := by
 decide +kernel
def cuts42596 : List PrefixCut := [⟨64,298596679,298596851⟩]
theorem checked42596 : checkPrefixCuts (2^48) 5587075073 10 Manual.Count131072.C042596.packed 64 cuts42596 = true := by
 decide +kernel
def cuts42597 : List PrefixCut := [⟨18,85038577,85038627⟩,
⟨64,293501537,293501709⟩]
theorem checked42597 : checkPrefixCuts (2^48) 5587206145 10 Manual.Count131072.C042597.packed 64 cuts42597 = true := by
 decide +kernel
def pointBounds42597 : List (Nat × Nat × Nat) := [(5587243008,109655737814005,109656123784677)]
theorem point_links_checked42597 : (cuts42597.take 1).map (fun c => (5587206145-1+2*2^10*c.k,109655652775428+c.lower,109656038746050+c.upper)) = pointBounds42597 := by
 decide +kernel
def cuts42598 : List PrefixCut := [⟨40,184581034,184581143⟩,
⟨64,296214978,296215152⟩]
theorem checked42598 : checkPrefixCuts (2^48) 5587337217 10 Manual.Count131072.C042598.packed 64 cuts42598 = true := by
 decide +kernel
def pointBounds42598 : List (Nat × Nat × Nat) := [(5587419136,109656130857999,109656516828902)]
theorem point_links_checked42598 : (cuts42598.take 1).map (fun c => (5587337217-1+2*2^10*c.k,109655946276965+c.lower,109656332247759+c.upper)) = pointBounds42598 := by
 decide +kernel
def cuts42599 : List PrefixCut := [⟨62,282757859,282758024⟩,
⟨64,291926098,291926269⟩]
theorem checked42599 : checkPrefixCuts (2^48) 5587468289 10 Manual.Count131072.C042599.packed 64 cuts42599 = true := by
 decide +kernel
def pointBounds42599 : List (Nat × Nat × Nat) := [(5587595264,109656525249802,109656911220935)]
theorem point_links_checked42599 : (cuts42599.take 1).map (fun c => (5587468289-1+2*2^10*c.k,109656242491943+c.lower,109656628462911+c.upper)) = pointBounds42599 := by
 decide +kernel
def cuts42600 : List PrefixCut := [⟨64,295898848,295899022⟩]
theorem checked42600 : checkPrefixCuts (2^48) 5587599361 10 Manual.Count131072.C042600.packed 64 cuts42600 = true := by
 decide +kernel
def cuts42601 : List PrefixCut := [⟨20,91931737,91931790⟩,
⟨64,290904948,290905118⟩]
theorem checked42601 : checkPrefixCuts (2^48) 5587730433 10 Manual.Count131072.C042601.packed 64 cuts42601 = true := by
 decide +kernel
def pointBounds42601 : List (Nat × Nat × Nat) := [(5587771392,109656922248626,109657308219992)]
theorem point_links_checked42601 : (cuts42601.take 1).map (fun c => (5587730433-1+2*2^10*c.k,109656830316889+c.lower,109657216288202+c.upper)) = pointBounds42601 := by
 decide +kernel
def cuts42602 : List PrefixCut := [⟨42,195544783,195544890⟩,
⟨64,294927915,294928082⟩]
theorem checked42602 : checkPrefixCuts (2^48) 5587861505 10 Manual.Count131072.C042602.packed 64 cuts42602 = true := by
 decide +kernel
def pointBounds42602 : List (Nat × Nat × Nat) := [(5587947520,109657316766620,109657702738210)]
theorem point_links_checked42602 : (cuts42602.take 1).map (fun c => (5587861505-1+2*2^10*c.k,109657121221837+c.lower,109657507193320+c.upper)) = pointBounds42602 := by
 decide +kernel
def cuts42603 : List PrefixCut := [⟨64,293460227,293460392⟩]
theorem checked42603 : checkPrefixCuts (2^48) 5587992577 10 Manual.Count131072.C042603.packed 64 cuts42603 = true := by
 decide +kernel
def pointBounds42603 : List (Nat × Nat × Nat) := [(5588123648,109657709609979,109658095581794)]
theorem point_links_checked42603 : (cuts42603.take 1).map (fun c => (5587992577-1+2*2^10*c.k,109657416149752+c.lower,109657802121402+c.upper)) = pointBounds42603 := by
 decide +kernel
def cuts42604 : List PrefixCut := [⟨64,293251871,293252034⟩]
theorem checked42604 : checkPrefixCuts (2^48) 5588123649 10 Manual.Count131072.C042604.packed 64 cuts42604 = true := by
 decide +kernel
def cuts42605 : List PrefixCut := [⟨22,103961236,103961298⟩,
⟨64,297929259,297929435⟩]
theorem checked42605 : checkPrefixCuts (2^48) 5588254721 10 Manual.Count131072.C042605.packed 64 cuts42605 = true := by
 decide +kernel
def pointBounds42605 : List (Nat × Nat × Nat) := [(5588299776,109658106823086,109658492795126)]
theorem point_links_checked42605 : (cuts42605.take 1).map (fun c => (5588254721-1+2*2^10*c.k,109658002861850+c.lower,109658388833828+c.upper)) = pointBounds42605 := by
 decide +kernel
def cuts42606 : List PrefixCut := [⟨44,201872665,201872782⟩,
⟨64,294749114,294749287⟩]
theorem checked42606 : checkPrefixCuts (2^48) 5588385793 10 Manual.Count131072.C042606.packed 64 cuts42606 = true := by
 decide +kernel
def pointBounds42606 : List (Nat × Nat × Nat) := [(5588475904,109658502663774,109658888636045)]
theorem point_links_checked42606 : (cuts42606.take 1).map (fun c => (5588385793-1+2*2^10*c.k,109658300791109+c.lower,109658686763263+c.upper)) = pointBounds42606 := by
 decide +kernel
def cuts42607 : List PrefixCut := [⟨64,293583774,293583947⟩]
theorem checked42607 : checkPrefixCuts (2^48) 5588516865 10 Manual.Count131072.C042607.packed 64 cuts42607 = true := by
 decide +kernel
def cuts42608 : List PrefixCut := [⟨2,9468706,9468710⟩,
⟨64,294332353,294332521⟩]
theorem checked42608 : checkPrefixCuts (2^48) 5588647937 10 Manual.Count131072.C042608.packed 64 cuts42608 = true := by
 decide +kernel
def pointBounds42608 : List (Nat × Nat × Nat) := [(5588652032,109658898592703,109659284565207)]
theorem point_links_checked42608 : (cuts42608.take 1).map (fun c => (5588647937-1+2*2^10*c.k,109658889123997+c.lower,109659275096497+c.upper)) = pointBounds42608 := by
 decide +kernel
def cuts42609 : List PrefixCut := [⟨24,108685668,108685731⟩,
⟨64,292814546,292814719⟩]
theorem checked42609 : checkPrefixCuts (2^48) 5588779009 10 Manual.Count131072.C042609.packed 64 cuts42609 = true := by
 decide +kernel
def pointBounds42609 : List (Nat × Nat × Nat) := [(5588828160,109659292142018,109659678114749)]
theorem point_links_checked42609 : (cuts42609.take 1).map (fun c => (5588779009-1+2*2^10*c.k,109659183456350+c.lower,109659569429018+c.upper)) = pointBounds42609 := by
 decide +kernel
def cuts42610 : List PrefixCut := [⟨46,210364924,210365038⟩,
⟨64,291800432,291800591⟩]
theorem checked42610 : checkPrefixCuts (2^48) 5588910081 10 Manual.Count131072.C042610.packed 64 cuts42610 = true := by
 decide +kernel
def pointBounds42610 : List (Nat × Nat × Nat) := [(5589004288,109659686635820,109660072608775)]
theorem point_links_checked42610 : (cuts42610.take 1).map (fun c => (5588910081-1+2*2^10*c.k,109659476270896+c.lower,109659862243737+c.upper)) = pointBounds42610 := by
 decide +kernel
def cuts42611 : List PrefixCut := [⟨64,294966349,294966519⟩]
theorem checked42611 : checkPrefixCuts (2^48) 5589041153 10 Manual.Count131072.C042611.packed 64 cuts42611 = true := by
 decide +kernel
def cuts42612 : List PrefixCut := [⟨4,17424805,17424817⟩,
⟨64,293549332,293549509⟩]
theorem checked42612 : checkPrefixCuts (2^48) 5589172225 10 Manual.Count131072.C042612.packed 64 cuts42612 = true := by
 decide +kernel
def pointBounds42612 : List (Nat × Nat × Nat) := [(5589180416,109660080462482,109660466435664)]
theorem point_links_checked42612 : (cuts42612.take 1).map (fun c => (5589172225-1+2*2^10*c.k,109660063037677+c.lower,109660449010847+c.upper)) = pointBounds42612 := by
 decide +kernel
def cuts42613 : List PrefixCut := [⟨26,118948727,118948796⟩,
⟨64,290520947,290521117⟩]
theorem checked42613 : checkPrefixCuts (2^48) 5589303297 10 Manual.Count131072.C042613.packed 64 cuts42613 = true := by
 decide +kernel
def pointBounds42613 : List (Nat × Nat × Nat) := [(5589356544,109660475535736,109660861509152)]
theorem point_links_checked42613 : (cuts42613.take 1).map (fun c => (5589303297-1+2*2^10*c.k,109660356587009+c.lower,109660742560356+c.upper)) = pointBounds42613 := by
 decide +kernel
def cuts42614 : List PrefixCut := [⟨48,220064220,220064347⟩,
⟨64,292830594,292830761⟩]
theorem checked42614 : checkPrefixCuts (2^48) 5589434369 10 Manual.Count131072.C042614.packed 64 cuts42614 = true := by
 decide +kernel
def pointBounds42614 : List (Nat × Nat × Nat) := [(5589532672,109660867172176,109661253145820)]
theorem point_links_checked42614 : (cuts42614.take 1).map (fun c => (5589434369-1+2*2^10*c.k,109660647107956+c.lower,109661033081473+c.upper)) = pointBounds42614 := by
 decide +kernel
def cuts42615 : List PrefixCut := [⟨64,293981895,293982070⟩]
theorem checked42615 : checkPrefixCuts (2^48) 5589565441 10 Manual.Count131072.C042615.packed 64 cuts42615 = true := by
 decide +kernel
def cuts42616 : List PrefixCut := [⟨6,27393646,27393662⟩,
⟨64,299363053,299363231⟩]
theorem checked42616 : checkPrefixCuts (2^48) 5589696513 10 Manual.Count131072.C042616.packed 64 cuts42616 = true := by
 decide +kernel
def pointBounds42616 : List (Nat × Nat × Nat) := [(5589708800,109661261314091,109661647287966)]
theorem point_links_checked42616 : (cuts42616.take 1).map (fun c => (5589696513-1+2*2^10*c.k,109661233920445+c.lower,109661619894304+c.upper)) = pointBounds42616 := by
 decide +kernel
def cuts42617 : List PrefixCut := [⟨28,128958101,128958176⟩,
⟨64,297543268,297543441⟩]
theorem checked42617 : checkPrefixCuts (2^48) 5589827585 10 Manual.Count131072.C042617.packed 64 cuts42617 = true := by
 decide +kernel
def pointBounds42617 : List (Nat × Nat × Nat) := [(5589884928,109661662241599,109662048215711)]
theorem point_links_checked42617 : (cuts42617.take 1).map (fun c => (5589827585-1+2*2^10*c.k,109661533283498+c.lower,109661919257535+c.upper)) = pointBounds42617 := by
 decide +kernel
def cuts42618 : List PrefixCut := [⟨50,232581456,232581592⟩,
⟨64,295874682,295874858⟩]
theorem checked42618 : checkPrefixCuts (2^48) 5589958657 10 Manual.Count131072.C042618.packed 64 cuts42618 = true := by
 decide +kernel
def pointBounds42618 : List (Nat × Nat × Nat) := [(5590061056,109662063408222,109662449382568)]
theorem point_links_checked42618 : (cuts42618.take 1).map (fun c => (5589958657-1+2*2^10*c.k,109661830826766+c.lower,109662216800976+c.upper)) = pointBounds42618 := by
 decide +kernel
def cuts42619 : List PrefixCut := [⟨64,290882899,290883073⟩]
theorem checked42619 : checkPrefixCuts (2^48) 5590089729 10 Manual.Count131072.C042619.packed 64 cuts42619 = true := by
 decide +kernel
def cuts42620 : List PrefixCut := [⟨8,37410961,37410983⟩,
⟨64,292587993,292588168⟩]
theorem checked42620 : checkPrefixCuts (2^48) 5590220801 10 Manual.Count131072.C042620.packed 64 cuts42620 = true := by
 decide +kernel
def pointBounds42620 : List (Nat × Nat × Nat) := [(5590237184,109662454995308,109662840969890)]
theorem point_links_checked42620 : (cuts42620.take 1).map (fun c => (5590220801-1+2*2^10*c.k,109662417584347+c.lower,109662803558907+c.upper)) = pointBounds42620 := by
 decide +kernel
def cuts42621 : List PrefixCut := [⟨30,139720821,139720901⟩,
⟨64,297062232,297062402⟩]
theorem checked42621 : checkPrefixCuts (2^48) 5590351873 10 Manual.Count131072.C042621.packed 64 cuts42621 = true := by
 decide +kernel
def pointBounds42621 : List (Nat × Nat × Nat) := [(5590413312,109662849893161,109663235867976)]
theorem point_links_checked42621 : (cuts42621.take 1).map (fun c => (5590351873-1+2*2^10*c.k,109662710172340+c.lower,109663096147075+c.upper)) = pointBounds42621 := by
 decide +kernel
def cuts42622 : List PrefixCut := [⟨52,234724530,234724667⟩,
⟨64,290661017,290661187⟩]
theorem checked42622 : checkPrefixCuts (2^48) 5590482945 10 Manual.Count131072.C042622.packed 64 cuts42622 = true := by
 decide +kernel
def pointBounds42622 : List (Nat × Nat × Nat) := [(5590589440,109663241959102,109663627934144)]
theorem point_links_checked42622 : (cuts42622.take 1).map (fun c => (5590482945-1+2*2^10*c.k,109663007234572+c.lower,109663393209477+c.upper)) = pointBounds42622 := by
 decide +kernel
def cuts42623 : List PrefixCut := [⟨64,296494467,296494637⟩]
theorem checked42623 : checkPrefixCuts (2^48) 5590614017 10 Manual.Count131072.C042623.packed 64 cuts42623 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000081
