import PlattAssemblyKernel
import PlattCertificates.Count131072.C028672
import PlattCertificates.Count131072.C028673
import PlattCertificates.Count131072.C028674
import PlattCertificates.Count131072.C028675
import PlattCertificates.Count131072.C028676
import PlattCertificates.Count131072.C028677
import PlattCertificates.Count131072.C028678
import PlattCertificates.Count131072.C028679
import PlattCertificates.Count131072.C028680
import PlattCertificates.Count131072.C028681
import PlattCertificates.Count131072.C028682
import PlattCertificates.Count131072.C028683
import PlattCertificates.Count131072.C028684
import PlattCertificates.Count131072.C028685
import PlattCertificates.Count131072.C028686
import PlattCertificates.Count131072.C028687
import PlattCertificates.Count131072.C028688
import PlattCertificates.Count131072.C028689
import PlattCertificates.Count131072.C028690
import PlattCertificates.Count131072.C028691
import PlattCertificates.Count131072.C028692
import PlattCertificates.Count131072.C028693
import PlattCertificates.Count131072.C028694
import PlattCertificates.Count131072.C028695
import PlattCertificates.Count131072.C028696
import PlattCertificates.Count131072.C028697
import PlattCertificates.Count131072.C028698
import PlattCertificates.Count131072.C028699
import PlattCertificates.Count131072.C028700
import PlattCertificates.Count131072.C028701
import PlattCertificates.Count131072.C028702
import PlattCertificates.Count131072.C028703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000271
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28672 : List PrefixCut := [⟨41,145898148,145898228⟩,
⟨128,449510632,449510881⟩]
theorem checked28672 : checkPrefixCuts (2^48) 3762028545 9 Manual.Count131072.C028672.packed 128 cuts28672 = true := by
 decide +kernel
def pointBounds28672 : List (Nat × Nat × Nat) := [(3762070528,104651356370932,104651739368904)]
theorem point_links_checked28672 : (cuts28672.take 1).map (fun c => (3762028545-1+2*2^9*c.k,104651210472784+c.lower,104651593470676+c.upper)) = pointBounds28672 := by
 decide +kernel
def cuts28673 : List PrefixCut := [⟨28,96514040,96514094⟩,
⟨128,446876340,446876589⟩]
theorem checked28673 : checkPrefixCuts (2^48) 3762159617 9 Manual.Count131072.C028673.packed 128 cuts28673 = true := by
 decide +kernel
def pointBounds28673 : List (Nat × Nat × Nat) := [(3762188288,104651756497456,104652139495651)]
theorem point_links_checked28673 : (cuts28673.take 1).map (fun c => (3762159617-1+2*2^9*c.k,104651659983416+c.lower,104652042981557+c.upper)) = pointBounds28673 := by
 decide +kernel
def cuts28674 : List PrefixCut := [⟨15,53492450,53492479⟩,
⟨128,440950577,440950827⟩]
theorem checked28674 : checkPrefixCuts (2^48) 3762290689 9 Manual.Count131072.C028674.packed 128 cuts28674 = true := by
 decide +kernel
def pointBounds28674 : List (Nat × Nat × Nat) := [(3762306048,104652160352206,104652543350625)]
theorem point_links_checked28674 : (cuts28674.take 1).map (fun c => (3762290689-1+2*2^9*c.k,104652106859756+c.lower,104652489858146+c.upper)) = pointBounds28674 := by
 decide +kernel
def cuts28675 : List PrefixCut := [⟨2,6658281,6658285⟩,
⟨117,406223568,406223798⟩,
⟨128,444226876,444227128⟩]
theorem checked28675 : checkPrefixCuts (2^48) 3762421761 9 Manual.Count131072.C028675.packed 128 cuts28675 = true := by
 decide +kernel
def pointBounds28675 : List (Nat × Nat × Nat) := [(3762423808,104652554468614,104652937467258),(3762541568,104652954033901,104653337032771)]
theorem point_links_checked28675 : (cuts28675.take 2).map (fun c => (3762421761-1+2*2^9*c.k,104652547810333+c.lower,104652930808973+c.upper)) = pointBounds28675 := by
 decide +kernel
def cuts28676 : List PrefixCut := [⟨104,356986151,356986355⟩,
⟨128,441518273,441518526⟩]
theorem checked28676 : checkPrefixCuts (2^48) 3762552833 9 Manual.Count131072.C028676.packed 128 cuts28676 = true := by
 decide +kernel
def pointBounds28676 : List (Nat × Nat × Nat) := [(3762659328,104653349023360,104653732022456)]
theorem point_links_checked28676 : (cuts28676.take 1).map (fun c => (3762552833-1+2*2^9*c.k,104652992037209+c.lower,104653375036101+c.upper)) = pointBounds28676 := by
 decide +kernel
def cuts28677 : List PrefixCut := [⟨91,317850817,317850993⟩,
⟨128,448385055,448385302⟩]
theorem checked28677 : checkPrefixCuts (2^48) 3762683905 9 Manual.Count131072.C028677.packed 128 cuts28677 = true := by
 decide +kernel
def pointBounds28677 : List (Nat × Nat × Nat) := [(3762777088,104653751406299,104654134405620)]
theorem point_links_checked28677 : (cuts28677.take 1).map (fun c => (3762683905-1+2*2^9*c.k,104653433555482+c.lower,104653816554627+c.upper)) = pointBounds28677 := by
 decide +kernel
def cuts28678 : List PrefixCut := [⟨78,268843937,268844090⟩,
⟨128,442459957,442460205⟩]
theorem checked28678 : checkPrefixCuts (2^48) 3762814977 9 Manual.Count131072.C028678.packed 128 cuts28678 = true := by
 decide +kernel
def pointBounds28678 : List (Nat × Nat × Nat) := [(3762894848,104654150784474,104654533784019)]
theorem point_links_checked28678 : (cuts28678.take 1).map (fun c => (3762814977-1+2*2^9*c.k,104653881940537+c.lower,104654264939929+c.upper)) = pointBounds28678 := by
 decide +kernel
def cuts28679 : List PrefixCut := [⟨65,224029259,224029385⟩,
⟨128,442220198,442220443⟩]
theorem checked28679 : checkPrefixCuts (2^48) 3762946049 9 Manual.Count131072.C028679.packed 128 cuts28679 = true := by
 decide +kernel
def pointBounds28679 : List (Nat × Nat × Nat) := [(3763012608,104654548429753,104654931429519)]
theorem point_links_checked28679 : (cuts28679.take 1).map (fun c => (3762946049-1+2*2^9*c.k,104654324400494+c.lower,104654707400134+c.upper)) = pointBounds28679 := by
 decide +kernel
def cuts28680 : List PrefixCut := [⟨52,182732972,182733073⟩,
⟨128,442279597,442279847⟩]
theorem checked28680 : checkPrefixCuts (2^48) 3763077121 9 Manual.Count131072.C028680.packed 128 cuts28680 = true := by
 decide +kernel
def pointBounds28680 : List (Nat × Nat × Nat) := [(3763130368,104654949353664,104655332353650)]
theorem point_links_checked28680 : (cuts28680.take 1).map (fun c => (3763077121-1+2*2^9*c.k,104654766620692+c.lower,104655149620577+c.upper)) = pointBounds28680 := by
 decide +kernel
def cuts28681 : List PrefixCut := [⟨39,136652526,136652600⟩,
⟨128,447948581,447948826⟩]
theorem checked28681 : checkPrefixCuts (2^48) 3763208193 9 Manual.Count131072.C028681.packed 128 cuts28681 = true := by
 decide +kernel
def pointBounds28681 : List (Nat × Nat × Nat) := [(3763248128,104655345552815,104655728553024)]
theorem point_links_checked28681 : (cuts28681.take 1).map (fun c => (3763208193-1+2*2^9*c.k,104655208900289+c.lower,104655591900424+c.upper)) = pointBounds28681 := by
 decide +kernel
def cuts28682 : List PrefixCut := [⟨26,91098668,91098720⟩,
⟨128,446063203,446063456⟩]
theorem checked28682 : checkPrefixCuts (2^48) 3763339265 9 Manual.Count131072.C028682.packed 128 cuts28682 = true := by
 decide +kernel
def pointBounds28682 : List (Nat × Nat × Nat) := [(3763365888,104655747947538,104656130947970)]
theorem point_links_checked28682 : (cuts28682.take 1).map (fun c => (3763339265-1+2*2^9*c.k,104655656848870+c.lower,104656039849250+c.upper)) = pointBounds28682 := by
 decide +kernel
def cuts28683 : List PrefixCut := [⟨13,42331812,42331837⟩,
⟨128,441560204,441560455⟩]
theorem checked28683 : checkPrefixCuts (2^48) 3763470337 9 Manual.Count131072.C028683.packed 128 cuts28683 = true := by
 decide +kernel
def pointBounds28683 : List (Nat × Nat × Nat) := [(3763483648,104656145243885,104656528244543),(3763601408,104656544472277,104656927473161)]
theorem point_links_checked28683 : (cuts28683.take 2).map (fun c => (3763470337-1+2*2^9*c.k,104656102912073+c.lower,104656485912706+c.upper)) = pointBounds28683 := by
 decide +kernel
def cuts28684 : List PrefixCut := [⟨115,404301427,404301654⟩,
⟨128,449173171,449173424⟩]
theorem checked28684 : checkPrefixCuts (2^48) 3763601409 9 Manual.Count131072.C028684.packed 128 cuts28684 = true := by
 decide +kernel
def pointBounds28684 : List (Nat × Nat × Nat) := [(3763719168,104656948773704,104657331774815)]
theorem point_links_checked28684 : (cuts28684.take 1).map (fun c => (3763601409-1+2*2^9*c.k,104656544472277+c.lower,104656927473161+c.upper)) = pointBounds28684 := by
 decide +kernel
def cuts28685 : List PrefixCut := [⟨102,351265457,351265651⟩,
⟨128,444296460,444296707⟩]
theorem checked28685 : checkPrefixCuts (2^48) 3763732481 9 Manual.Count131072.C028685.packed 128 cuts28685 = true := by
 decide +kernel
def pointBounds28685 : List (Nat × Nat × Nat) := [(3763836928,104657344910905,104657727912236)]
theorem point_links_checked28685 : (cuts28685.take 1).map (fun c => (3763732481-1+2*2^9*c.k,104656993645448+c.lower,104657376646585+c.upper)) = pointBounds28685 := by
 decide +kernel
def cuts28686 : List PrefixCut := [⟨89,306608612,306608785⟩,
⟨128,438971497,438971744⟩]
theorem checked28686 : checkPrefixCuts (2^48) 3763863553 9 Manual.Count131072.C028686.packed 128 cuts28686 = true := by
 decide +kernel
def pointBounds28686 : List (Nat × Nat × Nat) := [(3763954688,104657744550520,104658127552077)]
theorem point_links_checked28686 : (cuts28686.take 1).map (fun c => (3763863553-1+2*2^9*c.k,104657437941908+c.lower,104657820943292+c.upper)) = pointBounds28686 := by
 decide +kernel
def cuts28687 : List PrefixCut := [⟨76,263899043,263899192⟩,
⟨128,445611567,445611815⟩]
theorem checked28687 : checkPrefixCuts (2^48) 3763994625 9 Manual.Count131072.C028687.packed 128 cuts28687 = true := by
 decide +kernel
def pointBounds28687 : List (Nat × Nat × Nat) := [(3764072448,104658140812448,104658523814228)]
theorem point_links_checked28687 : (cuts28687.take 1).map (fun c => (3763994625-1+2*2^9*c.k,104657876913405+c.lower,104658259915036+c.upper)) = pointBounds28687 := by
 decide +kernel
def cuts28688 : List PrefixCut := [⟨63,216182170,216182292⟩,
⟨128,446044663,446044913⟩]
theorem checked28688 : checkPrefixCuts (2^48) 3764125697 9 Manual.Count131072.C028688.packed 128 cuts28688 = true := by
 decide +kernel
def pointBounds28688 : List (Nat × Nat × Nat) := [(3764190208,104658538707142,104658921709143)]
theorem point_links_checked28688 : (cuts28688.take 1).map (fun c => (3764125697-1+2*2^9*c.k,104658322524972+c.lower,104658705526851+c.upper)) = pointBounds28688 := by
 decide +kernel
def cuts28689 : List PrefixCut := [⟨50,173927082,173927178⟩,
⟨128,448272475,448272725⟩]
theorem checked28689 : checkPrefixCuts (2^48) 3764256769 9 Manual.Count131072.C028689.packed 128 cuts28689 = true := by
 decide +kernel
def pointBounds28689 : List (Nat × Nat × Nat) := [(3764307968,104658942496717,104659325498942)]
theorem point_links_checked28689 : (cuts28689.take 1).map (fun c => (3764256769-1+2*2^9*c.k,104658768569635+c.lower,104659151571764+c.upper)) = pointBounds28689 := by
 decide +kernel
def cuts28690 : List PrefixCut := [⟨37,125618146,125618217⟩,
⟨128,443770489,443770736⟩]
theorem checked28690 : checkPrefixCuts (2^48) 3764387841 9 Manual.Count131072.C028690.packed 128 cuts28690 = true := by
 decide +kernel
def pointBounds28690 : List (Nat × Nat × Nat) := [(3764425728,104659342460256,104659725462706)]
theorem point_links_checked28690 : (cuts28690.take 1).map (fun c => (3764387841-1+2*2^9*c.k,104659216842110+c.lower,104659599844489+c.upper)) = pointBounds28690 := by
 decide +kernel
def cuts28691 : List PrefixCut := [⟨24,84714679,84714728⟩,
⟨128,438521322,438521568⟩]
theorem checked28691 : checkPrefixCuts (2^48) 3764518913 9 Manual.Count131072.C028691.packed 128 cuts28691 = true := by
 decide +kernel
def pointBounds28691 : List (Nat × Nat × Nat) := [(3764543488,104659745327278,104660128329953)]
theorem point_links_checked28691 : (cuts28691.take 1).map (fun c => (3764518913-1+2*2^9*c.k,104659660612599+c.lower,104660043615225+c.upper)) = pointBounds28691 := by
 decide +kernel
def cuts28692 : List PrefixCut := [⟨11,36486668,36486690⟩,
⟨126,436337839,436338086⟩,
⟨128,443365776,443366027⟩]
theorem checked28692 : checkPrefixCuts (2^48) 3764649985 9 Manual.Count131072.C028692.packed 128 cuts28692 = true := by
 decide +kernel
def pointBounds28692 : List (Nat × Nat × Nat) := [(3764661248,104660135620589,104660518623483),(3764779008,104660535471760,104660918474879)]
theorem point_links_checked28692 : (cuts28692.take 2).map (fun c => (3764649985-1+2*2^9*c.k,104660099133921+c.lower,104660482136793+c.upper)) = pointBounds28692 := by
 decide +kernel
def cuts28693 : List PrefixCut := [⟨113,391240676,391240899⟩,
⟨128,442378448,442378699⟩]
theorem checked28693 : checkPrefixCuts (2^48) 3764781057 9 Manual.Count131072.C028693.packed 128 cuts28693 = true := by
 decide +kernel
def pointBounds28693 : List (Nat × Nat × Nat) := [(3764896768,104660933740373,104661316743719)]
theorem point_links_checked28693 : (cuts28693.take 1).map (fun c => (3764781057-1+2*2^9*c.k,104660542499697+c.lower,104660925502820+c.upper)) = pointBounds28693 := by
 decide +kernel
def cuts28694 : List PrefixCut := [⟨100,352800264,352800461⟩,
⟨128,452231533,452231786⟩]
theorem checked28694 : checkPrefixCuts (2^48) 3764912129 9 Manual.Count131072.C028694.packed 128 cuts28694 = true := by
 decide +kernel
def pointBounds28694 : List (Nat × Nat × Nat) := [(3765014528,104661337678409,104661720681980)]
theorem point_links_checked28694 : (cuts28694.take 1).map (fun c => (3764912129-1+2*2^9*c.k,104660984878145+c.lower,104661367881519+c.upper)) = pointBounds28694 := by
 decide +kernel
def cuts28695 : List PrefixCut := [⟨87,301503801,301503969⟩,
⟨128,443095251,443095498⟩]
theorem checked28695 : checkPrefixCuts (2^48) 3765043201 9 Manual.Count131072.C028695.packed 128 cuts28695 = true := by
 decide +kernel
def pointBounds28695 : List (Nat × Nat × Nat) := [(3765132288,104661738613479,104662121617274)]
theorem point_links_checked28695 : (cuts28695.take 1).map (fun c => (3765043201-1+2*2^9*c.k,104661437109678+c.lower,104661820113305+c.upper)) = pointBounds28695 := by
 decide +kernel
def cuts28696 : List PrefixCut := [⟨74,260003871,260004019⟩,
⟨128,447415705,447415956⟩]
theorem checked28696 : checkPrefixCuts (2^48) 3765174273 9 Manual.Count131072.C028696.packed 128 cuts28696 = true := by
 decide +kernel
def pointBounds28696 : List (Nat × Nat × Nat) := [(3765250048,104662140208800,104662523212822)]
theorem point_links_checked28696 : (cuts28696.take 1).map (fun c => (3765174273-1+2*2^9*c.k,104661880204929+c.lower,104662263208803+c.upper)) = pointBounds28696 := by
 decide +kernel
def cuts28697 : List PrefixCut := [⟨61,213871890,213872010⟩,
⟨128,448969939,448970192⟩]
theorem checked28697 : checkPrefixCuts (2^48) 3765305345 9 Manual.Count131072.C028697.packed 128 cuts28697 = true := by
 decide +kernel
def pointBounds28697 : List (Nat × Nat × Nat) := [(3765367808,104662541492524,104662924496769)]
theorem point_links_checked28697 : (cuts28697.take 1).map (fun c => (3765305345-1+2*2^9*c.k,104662327620634+c.lower,104662710624759+c.upper)) = pointBounds28697 := by
 decide +kernel
def cuts28698 : List PrefixCut := [⟨48,164229659,164229752⟩,
⟨128,441105424,441105671⟩]
theorem checked28698 : checkPrefixCuts (2^48) 3765436417 9 Manual.Count131072.C028698.packed 128 cuts28698 = true := by
 decide +kernel
def pointBounds28698 : List (Nat × Nat × Nat) := [(3765485568,104662940820232,104663323824703)]
theorem point_links_checked28698 : (cuts28698.take 1).map (fun c => (3765436417-1+2*2^9*c.k,104662776590573+c.lower,104663159594951+c.upper)) = pointBounds28698 := by
 decide +kernel
def cuts28699 : List PrefixCut := [⟨35,122663611,122663681⟩,
⟨128,444678004,444678258⟩]
theorem checked28699 : checkPrefixCuts (2^48) 3765567489 9 Manual.Count131072.C028699.packed 128 cuts28699 = true := by
 decide +kernel
def pointBounds28699 : List (Nat × Nat × Nat) := [(3765603328,104663340359608,104663723364303)]
theorem point_links_checked28699 : (cuts28699.take 1).map (fun c => (3765567489-1+2*2^9*c.k,104663217695997+c.lower,104663600700622+c.upper)) = pointBounds28699 := by
 decide +kernel
def cuts28700 : List PrefixCut := [⟨22,75045820,75045862⟩,
⟨128,437711214,437711460⟩]
theorem checked28700 : checkPrefixCuts (2^48) 3765698561 9 Manual.Count131072.C028700.packed 128 cuts28700 = true := by
 decide +kernel
def pointBounds28700 : List (Nat × Nat × Nat) := [(3765721088,104663737419821,104664120424742)]
theorem point_links_checked28700 : (cuts28700.take 1).map (fun c => (3765698561-1+2*2^9*c.k,104663662374001+c.lower,104664045378880+c.upper)) = pointBounds28700 := by
 decide +kernel
def cuts28701 : List PrefixCut := [⟨9,31317887,31317905⟩,
⟨124,435603356,435603599⟩,
⟨128,449430607,449430858⟩]
theorem checked28701 : checkPrefixCuts (2^48) 3765829633 9 Manual.Count131072.C028701.packed 128 cuts28701 = true := by
 decide +kernel
def pointBounds28701 : List (Nat × Nat × Nat) := [(3765838848,104664131403102,104664514408245),(3765956608,104664535688571,104664918693939)]
theorem point_links_checked28701 : (cuts28701.take 2).map (fun c => (3765829633-1+2*2^9*c.k,104664100085215+c.lower,104664483090340+c.upper)) = pointBounds28701 := by
 decide +kernel
def cuts28702 : List PrefixCut := [⟨111,381476709,381476924⟩,
⟨128,441193514,441193760⟩]
theorem checked28702 : checkPrefixCuts (2^48) 3765960705 9 Manual.Count131072.C028702.packed 128 cuts28702 = true := by
 decide +kernel
def pointBounds28702 : List (Nat × Nat × Nat) := [(3766074368,104664930992531,104665313998122)]
theorem point_links_checked28702 : (cuts28702.take 1).map (fun c => (3765960705-1+2*2^9*c.k,104664549515822+c.lower,104664932521198+c.upper)) = pointBounds28702 := by
 decide +kernel
def cuts28703 : List PrefixCut := [⟨98,341180176,341180364⟩,
⟨128,444765605,444765849⟩]
theorem checked28703 : checkPrefixCuts (2^48) 3766091777 9 Manual.Count131072.C028703.packed 128 cuts28703 = true := by
 decide +kernel
def pointBounds28703 : List (Nat × Nat × Nat) := [(3766192128,104665331889512,104665714895322)]
theorem point_links_checked28703 : (cuts28703.take 1).map (fun c => (3766091777-1+2*2^9*c.k,104664990709336+c.lower,104665373714958+c.upper)) = pointBounds28703 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000271
