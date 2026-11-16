import PlattAssemblyKernel
import PlattCertificates.Count131072.C041696
import PlattCertificates.Count131072.C041697
import PlattCertificates.Count131072.C041698
import PlattCertificates.Count131072.C041699
import PlattCertificates.Count131072.C041700
import PlattCertificates.Count131072.C041701
import PlattCertificates.Count131072.C041702
import PlattCertificates.Count131072.C041703
import PlattCertificates.Count131072.C041704
import PlattCertificates.Count131072.C041705
import PlattCertificates.Count131072.C041706
import PlattCertificates.Count131072.C041707
import PlattCertificates.Count131072.C041708
import PlattCertificates.Count131072.C041709
import PlattCertificates.Count131072.C041710
import PlattCertificates.Count131072.C041711
import PlattCertificates.Count131072.C041712
import PlattCertificates.Count131072.C041713
import PlattCertificates.Count131072.C041714
import PlattCertificates.Count131072.C041715
import PlattCertificates.Count131072.C041716
import PlattCertificates.Count131072.C041717
import PlattCertificates.Count131072.C041718
import PlattCertificates.Count131072.C041719
import PlattCertificates.Count131072.C041720
import PlattCertificates.Count131072.C041721
import PlattCertificates.Count131072.C041722
import PlattCertificates.Count131072.C041723
import PlattCertificates.Count131072.C041724
import PlattCertificates.Count131072.C041725
import PlattCertificates.Count131072.C041726
import PlattCertificates.Count131072.C041727
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41696 : List PrefixCut := [⟨64,303904934,303905112⟩]
theorem checked41696 : checkPrefixCuts (2^48) 5469110273 10 Manual.Count131072.C041696.packed 64 cuts41696 = true := by
 decide +kernel
def cuts41697 : List PrefixCut := [⟨17,80491115,80491162⟩,
⟨64,300964153,300964329⟩]
theorem checked41697 : checkPrefixCuts (2^48) 5469241345 10 Manual.Count131072.C041697.packed 64 cuts41697 = true := by
 decide +kernel
def pointBounds41697 : List (Nat × Nat × Nat) := [(5469276160,109387974954419,109388360768285)]
theorem point_links_checked41697 : (cuts41697.take 1).map (fun c => (5469241345-1+2*2^10*c.k,109387894463304+c.lower,109388280277123+c.upper)) = pointBounds41697 := by
 decide +kernel
def cuts41698 : List PrefixCut := [⟨37,172248265,172248367⟩,
⟨64,298846911,298847087⟩]
theorem checked41698 : checkPrefixCuts (2^48) 5469372417 10 Manual.Count131072.C041698.packed 64 cuts41698 = true := by
 decide +kernel
def pointBounds41698 : List (Nat × Nat × Nat) := [(5469448192,109388367675722,109388753489819)]
theorem point_links_checked41698 : (cuts41698.take 1).map (fun c => (5469372417-1+2*2^10*c.k,109388195427457+c.lower,109388581241452+c.upper)) = pointBounds41698 := by
 decide +kernel
def cuts41699 : List PrefixCut := [⟨57,266779304,266779459⟩,
⟨64,301412854,301413027⟩]
theorem checked41699 : checkPrefixCuts (2^48) 5469503489 10 Manual.Count131072.C041699.packed 64 cuts41699 = true := by
 decide +kernel
def pointBounds41699 : List (Nat × Nat × Nat) := [(5469620224,109388761053672,109389146867998)]
theorem point_links_checked41699 : (cuts41699.take 1).map (fun c => (5469503489-1+2*2^10*c.k,109388494274368+c.lower,109388880088539+c.upper)) = pointBounds41699 := by
 decide +kernel
def cuts41700 : List PrefixCut := [⟨64,297803399,297803574⟩]
theorem checked41700 : checkPrefixCuts (2^48) 5469634561 10 Manual.Count131072.C041700.packed 64 cuts41700 = true := by
 decide +kernel
def cuts41701 : List PrefixCut := [⟨13,61083038,61083073⟩,
⟨64,301964474,301964651⟩]
theorem checked41701 : checkPrefixCuts (2^48) 5469765633 10 Manual.Count131072.C041701.packed 64 cuts41701 = true := by
 decide +kernel
def pointBounds41701 : List (Nat × Nat × Nat) := [(5469792256,109389154573659,109389540388213)]
theorem point_links_checked41701 : (cuts41701.take 1).map (fun c => (5469765633-1+2*2^10*c.k,109389093490621+c.lower,109389479305140+c.upper)) = pointBounds41701 := by
 decide +kernel
def cuts41702 : List PrefixCut := [⟨33,156331193,156331285⟩,
⟨64,299796013,299796191⟩]
theorem checked41702 : checkPrefixCuts (2^48) 5469896705 10 Manual.Count131072.C041702.packed 64 cuts41702 = true := by
 decide +kernel
def pointBounds41702 : List (Nat × Nat × Nat) := [(5469964288,109389551786288,109389937601076)]
theorem point_links_checked41702 : (cuts41702.take 1).map (fun c => (5469896705-1+2*2^10*c.k,109389395455095+c.lower,109389781269791+c.upper)) = pointBounds41702 := by
 decide +kernel
def cuts41703 : List PrefixCut := [⟨53,250956581,250956727⟩,
⟨64,302927688,302927865⟩]
theorem checked41703 : checkPrefixCuts (2^48) 5470027777 10 Manual.Count131072.C041703.packed 64 cuts41703 = true := by
 decide +kernel
def pointBounds41703 : List (Nat × Nat × Nat) := [(5470136320,109389946207689,109390332022709)]
theorem point_links_checked41703 : (cuts41703.take 1).map (fun c => (5470027777-1+2*2^10*c.k,109389695251108+c.lower,109390081065982+c.upper)) = pointBounds41703 := by
 decide +kernel
def cuts41704 : List PrefixCut := [⟨64,300965099,300965276⟩]
theorem checked41704 : checkPrefixCuts (2^48) 5470158849 10 Manual.Count131072.C041704.packed 64 cuts41704 = true := by
 decide +kernel
def cuts41705 : List PrefixCut := [⟨9,41318460,41318484⟩,
⟨64,297819160,297819329⟩]
theorem checked41705 : checkPrefixCuts (2^48) 5470289921 10 Manual.Count131072.C041705.packed 64 cuts41705 = true := by
 decide +kernel
def pointBounds41705 : List (Nat × Nat × Nat) := [(5470308352,109390340462355,109390726277607)]
theorem point_links_checked41705 : (cuts41705.take 1).map (fun c => (5470289921-1+2*2^10*c.k,109390299143895+c.lower,109390684959123+c.upper)) = pointBounds41705 := by
 decide +kernel
def cuts41706 : List PrefixCut := [⟨29,135734840,135734920⟩,
⟨64,298738181,298738362⟩]
theorem checked41706 : checkPrefixCuts (2^48) 5470420993 10 Manual.Count131072.C041706.packed 64 cuts41706 = true := by
 decide +kernel
def pointBounds41706 : List (Nat × Nat × Nat) := [(5470480384,109390732697895,109391118513372)]
theorem point_links_checked41706 : (cuts41706.take 1).map (fun c => (5470420993-1+2*2^10*c.k,109390596963055+c.lower,109390982778452+c.upper)) = pointBounds41706 := by
 decide +kernel
def cuts41707 : List PrefixCut := [⟨49,231175040,231175171⟩,
⟨64,300737675,300737849⟩]
theorem checked41707 : checkPrefixCuts (2^48) 5470552065 10 Manual.Count131072.C041707.packed 64 cuts41707 = true := by
 decide +kernel
def pointBounds41707 : List (Nat × Nat × Nat) := [(5470652416,109391126876276,109391512691985)]
theorem point_links_checked41707 : (cuts41707.take 1).map (fun c => (5470552065-1+2*2^10*c.k,109390895701236+c.lower,109391281516814+c.upper)) = pointBounds41707 := by
 decide +kernel
def cuts41708 : List PrefixCut := [⟨64,298929668,298929844⟩]
theorem checked41708 : checkPrefixCuts (2^48) 5470683137 10 Manual.Count131072.C041708.packed 64 cuts41708 = true := by
 decide +kernel
def cuts41709 : List PrefixCut := [⟨5,23255501,23255515⟩,
⟨64,305971104,305971287⟩]
theorem checked41709 : checkPrefixCuts (2^48) 5470814209 10 Manual.Count131072.C041709.packed 64 cuts41709 = true := by
 decide +kernel
def pointBounds41709 : List (Nat × Nat × Nat) := [(5470824448,109391518624080,109391904440022)]
theorem point_links_checked41709 : (cuts41709.take 1).map (fun c => (5470814209-1+2*2^10*c.k,109391495368579+c.lower,109391881184507+c.upper)) = pointBounds41709 := by
 decide +kernel
def cuts41710 : List PrefixCut := [⟨25,118898184,118898252⟩,
⟨64,301076221,301076397⟩]
theorem checked41710 : checkPrefixCuts (2^48) 5470945281 10 Manual.Count131072.C041710.packed 64 cuts41710 = true := by
 decide +kernel
def pointBounds41710 : List (Nat × Nat × Nat) := [(5470996480,109391920237867,109392306054046)]
theorem point_links_checked41710 : (cuts41710.take 1).map (fun c => (5470945281-1+2*2^10*c.k,109391801339683+c.lower,109392187155794+c.upper)) = pointBounds41710 := by
 decide +kernel
def cuts41711 : List PrefixCut := [⟨45,210059638,210059761⟩,
⟨64,300554491,300554669⟩]
theorem checked41711 : checkPrefixCuts (2^48) 5471076353 10 Manual.Count131072.C041711.packed 64 cuts41711 = true := by
 decide +kernel
def pointBounds41711 : List (Nat × Nat × Nat) := [(5471168512,109392312475542,109392698291952)]
theorem point_links_checked41711 : (cuts41711.take 1).map (fun c => (5471076353-1+2*2^10*c.k,109392102415904+c.lower,109392488232191+c.upper)) = pointBounds41711 := by
 decide +kernel
def cuts41712 : List PrefixCut := [⟨64,301833437,301833618⟩]
theorem checked41712 : checkPrefixCuts (2^48) 5471207425 10 Manual.Count131072.C041712.packed 64 cuts41712 = true := by
 decide +kernel
def cuts41713 : List PrefixCut := [⟨1,5093088,5093091⟩,
⟨64,303472452,303472625⟩]
theorem checked41713 : checkPrefixCuts (2^48) 5471338497 10 Manual.Count131072.C041713.packed 64 cuts41713 = true := by
 decide +kernel
def pointBounds41713 : List (Nat × Nat × Nat) := [(5471340544,109392709896920,109393095713569)]
theorem point_links_checked41713 : (cuts41713.take 1).map (fun c => (5471338497-1+2*2^10*c.k,109392704803832+c.lower,109393090620478+c.upper)) = pointBounds41713 := by
 decide +kernel
def cuts41714 : List PrefixCut := [⟨21,98720867,98720927⟩,
⟨64,304288266,304288451⟩]
theorem checked41714 : checkPrefixCuts (2^48) 5471469569 10 Manual.Count131072.C041714.packed 64 cuts41714 = true := by
 decide +kernel
def pointBounds41714 : List (Nat × Nat × Nat) := [(5471512576,109393106997151,109393492814030)]
theorem point_links_checked41714 : (cuts41714.take 1).map (fun c => (5471469569-1+2*2^10*c.k,109393008276284+c.lower,109393394093103+c.upper)) = pointBounds41714 := by
 decide +kernel
def cuts41715 : List PrefixCut := [⟨41,195995886,195995996⟩,
⟨64,301143067,301143241⟩]
theorem checked41715 : checkPrefixCuts (2^48) 5471600641 10 Manual.Count131072.C041715.packed 64 cuts41715 = true := by
 decide +kernel
def pointBounds41715 : List (Nat × Nat × Nat) := [(5471684608,109393508560436,109393894377550)]
theorem point_links_checked41715 : (cuts41715.take 1).map (fun c => (5471600641-1+2*2^10*c.k,109393312564550+c.lower,109393698381554+c.upper)) = pointBounds41715 := by
 decide +kernel
def cuts41716 : List PrefixCut := [⟨61,284623403,284623564⟩,
⟨64,298049359,298049528⟩]
theorem checked41716 : checkPrefixCuts (2^48) 5471731713 10 Manual.Count131072.C041716.packed 64 cuts41716 = true := by
 decide +kernel
def pointBounds41716 : List (Nat × Nat × Nat) := [(5471856640,109393898331020,109394284148359)]
theorem point_links_checked41716 : (cuts41716.take 1).map (fun c => (5471731713-1+2*2^10*c.k,109393613707617+c.lower,109393999524795+c.upper)) = pointBounds41716 := by
 decide +kernel
def cuts41717 : List PrefixCut := [⟨64,304883674,304883850⟩]
theorem checked41717 : checkPrefixCuts (2^48) 5471862785 10 Manual.Count131072.C041717.packed 64 cuts41717 = true := by
 decide +kernel
def cuts41718 : List PrefixCut := [⟨17,79216090,79216135⟩,
⟨64,305647970,305648148⟩]
theorem checked41718 : checkPrefixCuts (2^48) 5471993857 10 Manual.Count131072.C041718.packed 64 cuts41718 = true := by
 decide +kernel
def pointBounds41718 : List (Nat × Nat × Nat) := [(5472028672,109394295856740,109394681674308)]
theorem point_links_checked41718 : (cuts41718.take 1).map (fun c => (5471993857-1+2*2^10*c.k,109394216640650+c.lower,109394602458173+c.upper)) = pointBounds41718 := by
 decide +kernel
def cuts41719 : List PrefixCut := [⟨37,174733506,174733610⟩,
⟨64,303891760,303891939⟩]
theorem checked41719 : checkPrefixCuts (2^48) 5472124929 10 Manual.Count131072.C041719.packed 64 cuts41719 = true := by
 decide +kernel
def pointBounds41719 : List (Nat × Nat × Nat) := [(5472200704,109394697022126,109395082839931)]
theorem point_links_checked41719 : (cuts41719.take 1).map (fun c => (5472124929-1+2*2^10*c.k,109394522288620+c.lower,109394908106321+c.upper)) = pointBounds41719 := by
 decide +kernel
def cuts41720 : List PrefixCut := [⟨57,269011171,269011334⟩,
⟨64,302084233,302084416⟩]
theorem checked41720 : checkPrefixCuts (2^48) 5472256001 10 Manual.Count131072.C041720.packed 64 cuts41720 = true := by
 decide +kernel
def pointBounds41720 : List (Nat × Nat × Nat) := [(5472372736,109395095191551,109395481009594)]
theorem point_links_checked41720 : (cuts41720.take 1).map (fun c => (5472256001-1+2*2^10*c.k,109394826180380+c.lower,109395211998260+c.upper)) = pointBounds41720 := by
 decide +kernel
def cuts41721 : List PrefixCut := [⟨64,301511190,301511368⟩]
theorem checked41721 : checkPrefixCuts (2^48) 5472387073 10 Manual.Count131072.C041721.packed 64 cuts41721 = true := by
 decide +kernel
def cuts41722 : List PrefixCut := [⟨13,62801073,62801111⟩,
⟨64,297543632,297543811⟩]
theorem checked41722 : checkPrefixCuts (2^48) 5472518145 10 Manual.Count131072.C041722.packed 64 cuts41722 = true := by
 decide +kernel
def pointBounds41722 : List (Nat × Nat × Nat) := [(5472544768,109395492576876,109395878395155)]
theorem point_links_checked41722 : (cuts41722.take 1).map (fun c => (5472518145-1+2*2^10*c.k,109395429775803+c.lower,109395815594044+c.upper)) = pointBounds41722 := by
 decide +kernel
def cuts41723 : List PrefixCut := [⟨33,155481059,155481152⟩,
⟨64,303554032,303554213⟩]
theorem checked41723 : checkPrefixCuts (2^48) 5472649217 10 Manual.Count131072.C041723.packed 64 cuts41723 = true := by
 decide +kernel
def pointBounds41723 : List (Nat × Nat × Nat) := [(5472716800,109395882800494,109396268619007)]
theorem point_links_checked41723 : (cuts41723.take 1).map (fun c => (5472649217-1+2*2^10*c.k,109395727319435+c.lower,109396113137855+c.upper)) = pointBounds41723 := by
 decide +kernel
def cuts41724 : List PrefixCut := [⟨53,246715858,246716002⟩,
⟨64,298249384,298249560⟩]
theorem checked41724 : checkPrefixCuts (2^48) 5472780289 10 Manual.Count131072.C041724.packed 64 cuts41724 = true := by
 decide +kernel
def pointBounds41724 : List (Nat × Nat × Nat) := [(5472888832,109396277589325,109396663408070)]
theorem point_links_checked41724 : (cuts41724.take 1).map (fun c => (5472780289-1+2*2^10*c.k,109396030873467+c.lower,109396416692068+c.upper)) = pointBounds41724 := by
 decide +kernel
def cuts41725 : List PrefixCut := [⟨64,299888009,299888186⟩]
theorem checked41725 : checkPrefixCuts (2^48) 5472911361 10 Manual.Count131072.C041725.packed 64 cuts41725 = true := by
 decide +kernel
def cuts41726 : List PrefixCut := [⟨9,40320525,40320551⟩,
⟨64,298286529,298286707⟩]
theorem checked41726 : checkPrefixCuts (2^48) 5473042433 10 Manual.Count131072.C041726.packed 64 cuts41726 = true := by
 decide +kernel
def pointBounds41726 : List (Nat × Nat × Nat) := [(5473060864,109396669331385,109397055150365)]
theorem point_links_checked41726 : (cuts41726.take 1).map (fun c => (5473042433-1+2*2^10*c.k,109396629010860+c.lower,109397014829814+c.upper)) = pointBounds41726 := by
 decide +kernel
def cuts41727 : List PrefixCut := [⟨29,135975147,135975229⟩,
⟨64,302856425,302856603⟩]
theorem checked41727 : checkPrefixCuts (2^48) 5473173505 10 Manual.Count131072.C041727.packed 64 cuts41727 = true := by
 decide +kernel
def pointBounds41727 : List (Nat × Nat × Nat) := [(5473232896,109397063272536,109397449091750)]
theorem point_links_checked41727 : (cuts41727.take 1).map (fun c => (5473173505-1+2*2^10*c.k,109396927297389+c.lower,109397313116521+c.upper)) = pointBounds41727 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000053
