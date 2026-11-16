import PlattAssemblyKernel
import PlattCertificates.Count131072.C044672
import PlattCertificates.Count131072.C044673
import PlattCertificates.Count131072.C044674
import PlattCertificates.Count131072.C044675
import PlattCertificates.Count131072.C044676
import PlattCertificates.Count131072.C044677
import PlattCertificates.Count131072.C044678
import PlattCertificates.Count131072.C044679
import PlattCertificates.Count131072.C044680
import PlattCertificates.Count131072.C044681
import PlattCertificates.Count131072.C044682
import PlattCertificates.Count131072.C044683
import PlattCertificates.Count131072.C044684
import PlattCertificates.Count131072.C044685
import PlattCertificates.Count131072.C044686
import PlattCertificates.Count131072.C044687
import PlattCertificates.Count131072.C044688
import PlattCertificates.Count131072.C044689
import PlattCertificates.Count131072.C044690
import PlattCertificates.Count131072.C044691
import PlattCertificates.Count131072.C044692
import PlattCertificates.Count131072.C044693
import PlattCertificates.Count131072.C044694
import PlattCertificates.Count131072.C044695
import PlattCertificates.Count131072.C044696
import PlattCertificates.Count131072.C044697
import PlattCertificates.Count131072.C044698
import PlattCertificates.Count131072.C044699
import PlattCertificates.Count131072.C044700
import PlattCertificates.Count131072.C044701
import PlattCertificates.Count131072.C044702
import PlattCertificates.Count131072.C044703
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000146
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts44672 : List PrefixCut := [⟨64,280502289,280502458⟩]
theorem checked44672 : checkPrefixCuts (2^48) 5859180545 10 Manual.Count131072.C044672.packed 64 cuts44672 = true := by
 decide +kernel
def cuts44673 : List PrefixCut := [⟨21,94492173,94492226⟩,
⟨64,286837076,286837236⟩]
theorem checked44673 : checkPrefixCuts (2^48) 5859311617 10 Manual.Count131072.C044673.packed 64 cuts44673 = true := by
 decide +kernel
def pointBounds44673 : List (Nat × Nat × Nat) := [(5859354624,110251504047798,110251890364479)]
theorem point_links_checked44673 : (cuts44673.take 1).map (fun c => (5859311617-1+2*2^10*c.k,110251409555625+c.lower,110251795872253+c.upper)) = pointBounds44673 := by
 decide +kernel
def cuts44674 : List PrefixCut := [⟨47,206032559,206032680⟩,
⟨64,278904528,278904693⟩]
theorem checked44674 : checkPrefixCuts (2^48) 5859442689 10 Manual.Count131072.C044674.packed 64 cuts44674 = true := by
 decide +kernel
def pointBounds44674 : List (Nat × Nat × Nat) := [(5859538944,110251902425260,110252288742169)]
theorem point_links_checked44674 : (cuts44674.take 1).map (fun c => (5859442689-1+2*2^10*c.k,110251696392701+c.lower,110252082709489+c.upper)) = pointBounds44674 := by
 decide +kernel
def cuts44675 : List PrefixCut := [⟨64,282164748,282164916⟩]
theorem checked44675 : checkPrefixCuts (2^48) 5859573761 10 Manual.Count131072.C044675.packed 64 cuts44675 = true := by
 decide +kernel
def cuts44676 : List PrefixCut := [⟨9,40445980,40446002⟩,
⟨64,283071092,283071253⟩]
theorem checked44676 : checkPrefixCuts (2^48) 5859704833 10 Manual.Count131072.C044676.packed 64 cuts44676 = true := by
 decide +kernel
def pointBounds44676 : List (Nat × Nat × Nat) := [(5859723264,110252297907957,110252684225100)]
theorem point_links_checked44676 : (cuts44676.take 1).map (fun c => (5859704833-1+2*2^10*c.k,110252257461977+c.lower,110252643779098+c.upper)) = pointBounds44676 := by
 decide +kernel
def cuts44677 : List PrefixCut := [⟨35,151019860,151019952⟩,
⟨64,276628179,276628345⟩]
theorem checked44677 : checkPrefixCuts (2^48) 5859835905 10 Manual.Count131072.C044677.packed 64 cuts44677 = true := by
 decide +kernel
def pointBounds44677 : List (Nat × Nat × Nat) := [(5859907584,110252691552929,110253077870303)]
theorem point_links_checked44677 : (cuts44677.take 1).map (fun c => (5859835905-1+2*2^10*c.k,110252540533069+c.lower,110252926850351+c.upper)) = pointBounds44677 := by
 decide +kernel
def cuts44678 : List PrefixCut := [⟨61,264565861,264566007⟩,
⟨64,276814143,276814297⟩]
theorem checked44678 : checkPrefixCuts (2^48) 5859966977 10 Manual.Count131072.C044678.packed 64 cuts44678 = true := by
 decide +kernel
def pointBounds44678 : List (Nat × Nat × Nat) := [(5860091904,110253081727109,110253468044703)]
theorem point_links_checked44678 : (cuts44678.take 1).map (fun c => (5859966977-1+2*2^10*c.k,110252817161248+c.lower,110253203478696+c.upper)) = pointBounds44678 := by
 decide +kernel
def cuts44679 : List PrefixCut := [⟨64,281803288,281803449⟩]
theorem checked44679 : checkPrefixCuts (2^48) 5860098049 10 Manual.Count131072.C044679.packed 64 cuts44679 = true := by
 decide +kernel
def cuts44680 : List PrefixCut := [⟨23,100048961,100049018⟩,
⟨64,277810395,277810555⟩]
theorem checked44680 : checkPrefixCuts (2^48) 5860229121 10 Manual.Count131072.C044680.packed 64 cuts44680 = true := by
 decide +kernel
def pointBounds44680 : List (Nat × Nat × Nat) := [(5860276224,110253475827640,110253862145460)]
theorem point_links_checked44680 : (cuts44680.take 1).map (fun c => (5860229121-1+2*2^10*c.k,110253375778679+c.lower,110253762096442+c.upper)) = pointBounds44680 := by
 decide +kernel
def cuts44681 : List PrefixCut := [⟨49,218151794,218151923⟩,
⟨64,285440925,285441094⟩]
theorem checked44681 : checkPrefixCuts (2^48) 5860360193 10 Manual.Count131072.C044681.packed 64 cuts44681 = true := by
 decide +kernel
def pointBounds44681 : List (Nat × Nat × Nat) := [(5860460544,110253871740868,110254258058920)]
theorem point_links_checked44681 : (cuts44681.take 1).map (fun c => (5860360193-1+2*2^10*c.k,110253653589074+c.lower,110254039906997+c.upper)) = pointBounds44681 := by
 decide +kernel
def cuts44682 : List PrefixCut := [⟨64,280151367,280151530⟩]
theorem checked44682 : checkPrefixCuts (2^48) 5860491265 10 Manual.Count131072.C044682.packed 64 cuts44682 = true := by
 decide +kernel
def cuts44683 : List PrefixCut := [⟨11,49516937,49516966⟩,
⟨64,282978752,282978914⟩]
theorem checked44683 : checkPrefixCuts (2^48) 5860622337 10 Manual.Count131072.C044683.packed 64 cuts44683 = true := by
 decide +kernel
def pointBounds44683 : List (Nat × Nat × Nat) := [(5860644864,110254268698303,110254655016587)]
theorem point_links_checked44683 : (cuts44683.take 1).map (fun c => (5860622337-1+2*2^10*c.k,110254219181366+c.lower,110254605499621+c.upper)) = pointBounds44683 := by
 decide +kernel
def cuts44684 : List PrefixCut := [⟨37,161994308,161994398⟩,
⟨64,280282931,280283086⟩]
theorem checked44684 : checkPrefixCuts (2^48) 5860753409 10 Manual.Count131072.C044684.packed 64 cuts44684 = true := by
 decide +kernel
def pointBounds44684 : List (Nat × Nat × Nat) := [(5860829184,110254664154426,110255050472933)]
theorem point_links_checked44684 : (cuts44684.take 1).map (fun c => (5860753409-1+2*2^10*c.k,110254502160118+c.lower,110254888478535+c.upper)) = pointBounds44684 := by
 decide +kernel
def cuts44685 : List PrefixCut := [⟨63,276722828,276722988⟩,
⟨64,281477298,281477460⟩]
theorem checked44685 : checkPrefixCuts (2^48) 5860884481 10 Manual.Count131072.C044685.packed 64 cuts44685 = true := by
 decide +kernel
def pointBounds44685 : List (Nat × Nat × Nat) := [(5861013504,110255059165877,110255445484609)]
theorem point_links_checked44685 : (cuts44685.take 1).map (fun c => (5860884481-1+2*2^10*c.k,110254782443049+c.lower,110255168761621+c.upper)) = pointBounds44685 := by
 decide +kernel
def cuts44686 : List PrefixCut := [⟨64,276524511,276524669⟩]
theorem checked44686 : checkPrefixCuts (2^48) 5861015553 10 Manual.Count131072.C044686.packed 64 cuts44686 = true := by
 decide +kernel
def cuts44687 : List PrefixCut := [⟨25,109974162,109974228⟩,
⟨64,278871448,278871610⟩]
theorem checked44687 : checkPrefixCuts (2^48) 5861146625 10 Manual.Count131072.C044687.packed 64 cuts44687 = true := by
 decide +kernel
def pointBounds44687 : List (Nat × Nat × Nat) := [(5861197824,110255450419020,110255836737978)]
theorem point_links_checked44687 : (cuts44687.take 1).map (fun c => (5861146625-1+2*2^10*c.k,110255340444858+c.lower,110255726763750+c.upper)) = pointBounds44687 := by
 decide +kernel
def cuts44688 : List PrefixCut := [⟨51,221719241,221719368⟩,
⟨64,280209822,280209980⟩]
theorem checked44688 : checkPrefixCuts (2^48) 5861277697 10 Manual.Count131072.C044688.packed 64 cuts44688 = true := by
 decide +kernel
def pointBounds44688 : List (Nat × Nat × Nat) := [(5861382144,110255841035547,110256227354728)]
theorem point_links_checked44688 : (cuts44688.take 1).map (fun c => (5861277697-1+2*2^10*c.k,110255619316306+c.lower,110256005635360+c.upper)) = pointBounds44688 := by
 decide +kernel
def cuts44689 : List PrefixCut := [⟨64,285149742,285149901⟩]
theorem checked44689 : checkPrefixCuts (2^48) 5861408769 10 Manual.Count131072.C044689.packed 64 cuts44689 = true := by
 decide +kernel
def cuts44690 : List PrefixCut := [⟨13,53734972,53735005⟩,
⟨64,275971484,275971646⟩]
theorem checked44690 : checkPrefixCuts (2^48) 5861539841 10 Manual.Count131072.C044690.packed 64 cuts44690 = true := by
 decide +kernel
def pointBounds44690 : List (Nat × Nat × Nat) := [(5861566464,110256238410842,110256624730246)]
theorem point_links_checked44690 : (cuts44690.take 1).map (fun c => (5861539841-1+2*2^10*c.k,110256184675870+c.lower,110256570995241+c.upper)) = pointBounds44690 := by
 decide +kernel
def cuts44691 : List PrefixCut := [⟨39,171236609,171236707⟩,
⟨64,279326709,279326871⟩]
theorem checked44691 : checkPrefixCuts (2^48) 5861670913 10 Manual.Count131072.C044691.packed 64 cuts44691 = true := by
 decide +kernel
def pointBounds44691 : List (Nat × Nat × Nat) := [(5861750784,110256631883963,110257018203594)]
theorem point_links_checked44691 : (cuts44691.take 1).map (fun c => (5861670913-1+2*2^10*c.k,110256460647354+c.lower,110256846966887+c.upper)) = pointBounds44691 := by
 decide +kernel
def cuts44692 : List PrefixCut := [⟨64,278840286,278840446⟩]
theorem checked44692 : checkPrefixCuts (2^48) 5861801985 10 Manual.Count131072.C044692.packed 64 cuts44692 = true := by
 decide +kernel
def cuts44693 : List PrefixCut := [⟨1,4417602,4417604⟩,
⟨64,279026100,279026260⟩]
theorem checked44693 : checkPrefixCuts (2^48) 5861933057 10 Manual.Count131072.C044693.packed 64 cuts44693 = true := by
 decide +kernel
def pointBounds44693 : List (Nat × Nat × Nat) := [(5861935104,110257023231951,110257409551808)]
theorem point_links_checked44693 : (cuts44693.take 1).map (fun c => (5861933057-1+2*2^10*c.k,110257018814349+c.lower,110257405134204+c.upper)) = pointBounds44693 := by
 decide +kernel
def cuts44694 : List PrefixCut := [⟨27,113558127,113558195⟩,
⟨64,274890480,274890642⟩]
theorem checked44694 : checkPrefixCuts (2^48) 5862064129 10 Manual.Count131072.C044694.packed 64 cuts44694 = true := by
 decide +kernel
def pointBounds44694 : List (Nat × Nat × Nat) := [(5862119424,110257411398576,110257797718659)]
theorem point_links_checked44694 : (cuts44694.take 1).map (fun c => (5862064129-1+2*2^10*c.k,110257297840449+c.lower,110257684160464+c.upper)) = pointBounds44694 := by
 decide +kernel
def cuts44695 : List PrefixCut := [⟨53,231239405,231239540⟩,
⟨64,278437451,278437614⟩]
theorem checked44695 : checkPrefixCuts (2^48) 5862195201 10 Manual.Count131072.C044695.packed 64 cuts44695 = true := by
 decide +kernel
def pointBounds44695 : List (Nat × Nat × Nat) := [(5862303744,110257803970334,110258190290646)]
theorem point_links_checked44695 : (cuts44695.take 1).map (fun c => (5862195201-1+2*2^10*c.k,110257572730929+c.lower,110257959051106+c.upper)) = pointBounds44695 := by
 decide +kernel
def cuts44696 : List PrefixCut := [⟨64,284865056,284865218⟩]
theorem checked44696 : checkPrefixCuts (2^48) 5862326273 10 Manual.Count131072.C044696.packed 64 cuts44696 = true := by
 decide +kernel
def cuts44697 : List PrefixCut := [⟨15,65729794,65729835⟩,
⟨64,280441537,280441701⟩]
theorem checked44697 : checkPrefixCuts (2^48) 5862457345 10 Manual.Count131072.C044697.packed 64 cuts44697 = true := by
 decide +kernel
def pointBounds44697 : List (Nat × Nat × Nat) := [(5862488064,110258201763230,110258588083773)]
theorem point_links_checked44697 : (cuts44697.take 1).map (fun c => (5862457345-1+2*2^10*c.k,110258136033436+c.lower,110258522353938+c.upper)) = pointBounds44697 := by
 decide +kernel
def cuts44698 : List PrefixCut := [⟨41,179419742,179419849⟩,
⟨64,280291210,280291375⟩]
theorem checked44698 : checkPrefixCuts (2^48) 5862588417 10 Manual.Count131072.C044698.packed 64 cuts44698 = true := by
 decide +kernel
def pointBounds44698 : List (Nat × Nat × Nat) := [(5862672384,110258595894715,110258982215488)]
theorem point_links_checked44698 : (cuts44698.take 1).map (fun c => (5862588417-1+2*2^10*c.k,110258416474973+c.lower,110258802795639+c.upper)) = pointBounds44698 := by
 decide +kernel
def cuts44699 : List PrefixCut := [⟨64,278316497,278316657⟩]
theorem checked44699 : checkPrefixCuts (2^48) 5862719489 10 Manual.Count131072.C044699.packed 64 cuts44699 = true := by
 decide +kernel
def cuts44700 : List PrefixCut := [⟨3,13250727,13250734⟩,
⟨64,278022282,278022446⟩]
theorem checked44700 : checkPrefixCuts (2^48) 5862850561 10 Manual.Count131072.C044700.packed 64 cuts44700 = true := by
 decide +kernel
def pointBounds44700 : List (Nat × Nat × Nat) := [(5862856704,110258988333407,110259374654405)]
theorem point_links_checked44700 : (cuts44700.take 1).map (fun c => (5862850561-1+2*2^10*c.k,110258975082680+c.lower,110259361403671+c.upper)) = pointBounds44700 := by
 decide +kernel
def cuts44701 : List PrefixCut := [⟨29,125686493,125686564⟩,
⟨64,279216245,279216406⟩]
theorem checked44701 : checkPrefixCuts (2^48) 5862981633 10 Manual.Count131072.C044701.packed 64 cuts44701 = true := by
 decide +kernel
def pointBounds44701 : List (Nat × Nat × Nat) := [(5863041024,110259378791455,110259765112681)]
theorem point_links_checked44701 : (cuts44701.take 1).map (fun c => (5862981633-1+2*2^10*c.k,110259253104962+c.lower,110259639426117+c.upper)) = pointBounds44701 := by
 decide +kernel
def cuts44702 : List PrefixCut := [⟨55,241428690,241428831⟩,
⟨64,281274302,281274466⟩]
theorem checked44702 : checkPrefixCuts (2^48) 5863112705 10 Manual.Count131072.C044702.packed 64 cuts44702 = true := by
 decide +kernel
def pointBounds44702 : List (Nat × Nat × Nat) := [(5863225344,110259773749897,110260160071354)]
theorem point_links_checked44702 : (cuts44702.take 1).map (fun c => (5863112705-1+2*2^10*c.k,110259532321207+c.lower,110259918642523+c.upper)) = pointBounds44702 := by
 decide +kernel
def cuts44703 : List PrefixCut := [⟨64,277523529,277523691⟩]
theorem checked44703 : checkPrefixCuts (2^48) 5863243777 10 Manual.Count131072.C044703.packed 64 cuts44703 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000146
