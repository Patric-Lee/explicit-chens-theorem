import PlattAssemblyKernel
import PlattCertificates.Count131072.C067840
import PlattCertificates.Count131072.C067841
import PlattCertificates.Count131072.C067842
import PlattCertificates.Count131072.C067843
import PlattCertificates.Count131072.C067844
import PlattCertificates.Count131072.C067845
import PlattCertificates.Count131072.C067846
import PlattCertificates.Count131072.C067847
import PlattCertificates.Count131072.C067848
import PlattCertificates.Count131072.C067849
import PlattCertificates.Count131072.C067850
import PlattCertificates.Count131072.C067851
import PlattCertificates.Count131072.C067852
import PlattCertificates.Count131072.C067853
import PlattCertificates.Count131072.C067854
import PlattCertificates.Count131072.C067855
import PlattCertificates.Count131072.C067856
import PlattCertificates.Count131072.C067857
import PlattCertificates.Count131072.C067858
import PlattCertificates.Count131072.C067859
import PlattCertificates.Count131072.C067860
import PlattCertificates.Count131072.C067861
import PlattCertificates.Count131072.C067862
import PlattCertificates.Count131072.C067863
import PlattCertificates.Count131072.C067864
import PlattCertificates.Count131072.C067865
import PlattCertificates.Count131072.C067866
import PlattCertificates.Count131072.C067867
import PlattCertificates.Count131072.C067868
import PlattCertificates.Count131072.C067869
import PlattCertificates.Count131072.C067870
import PlattCertificates.Count131072.C067871
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000245
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67840 : List PrefixCut := [⟨64,181080812,181080918⟩]
theorem checked67840 : checkPrefixCuts (2^48) 8895856641 10 Manual.Count131072.C067840.packed 64 cuts67840 = true := by
 decide +kernel
def cuts67841 : List PrefixCut := [⟨53,149975793,149975881⟩,
⟨64,181489464,181489568⟩]
theorem checked67841 : checkPrefixCuts (2^48) 8895987713 10 Manual.Count131072.C067841.packed 64 cuts67841 = true := by
 decide +kernel
def pointBounds67841 : List (Nat × Nat × Nat) := [(8896096256,115429415691829,115429804971679)]
theorem point_links_checked67841 : (cuts67841.take 1).map (fun c => (8895987713-1+2*2^10*c.k,115429265716036+c.lower,115429654995798+c.upper)) = pointBounds67841 := by
 decide +kernel
def cuts67842 : List PrefixCut := [⟨64,180094643,180094754⟩]
theorem checked67842 : checkPrefixCuts (2^48) 8896118785 10 Manual.Count131072.C067842.packed 64 cuts67842 = true := by
 decide +kernel
def cuts67843 : List PrefixCut := [⟨61,171834136,171834244⟩,
⟨64,180914607,180914719⟩]
theorem checked67843 : checkPrefixCuts (2^48) 8896249857 10 Manual.Count131072.C067843.packed 64 cuts67843 = true := by
 decide +kernel
def pointBounds67843 : List (Nat × Nat × Nat) := [(8896374784,115429799134279,115430188414364)]
theorem point_links_checked67843 : (cuts67843.take 1).map (fun c => (8896249857-1+2*2^10*c.k,115429627300143+c.lower,115430016580120+c.upper)) = pointBounds67843 := by
 decide +kernel
def cuts67844 : List PrefixCut := [⟨64,179361619,179361725⟩]
theorem checked67844 : checkPrefixCuts (2^48) 8896380929 10 Manual.Count131072.C067844.packed 64 cuts67844 = true := by
 decide +kernel
def cuts67845 : List PrefixCut := [⟨64,181067467,181067571⟩]
theorem checked67845 : checkPrefixCuts (2^48) 8896512001 10 Manual.Count131072.C067845.packed 64 cuts67845 = true := by
 decide +kernel
def cuts67846 : List PrefixCut := [⟨5,13604472,13604480⟩,
⟨64,179324702,179324809⟩]
theorem checked67846 : checkPrefixCuts (2^48) 8896643073 10 Manual.Count131072.C067846.packed 64 cuts67846 = true := by
 decide +kernel
def pointBounds67846 : List (Nat × Nat × Nat) := [(8896653312,115430182248308,115430571528615)]
theorem point_links_checked67846 : (cuts67846.take 1).map (fun c => (8896643073-1+2*2^10*c.k,115430168643836+c.lower,115430557924135+c.upper)) = pointBounds67846 := by
 decide +kernel
def cuts67847 : List PrefixCut := [⟨64,179448613,179448717⟩]
theorem checked67847 : checkPrefixCuts (2^48) 8896774145 10 Manual.Count131072.C067847.packed 64 cuts67847 = true := by
 decide +kernel
def cuts67848 : List PrefixCut := [⟨13,36256401,36256421⟩,
⟨64,181027838,181027945⟩]
theorem checked67848 : checkPrefixCuts (2^48) 8896905217 10 Manual.Count131072.C067848.packed 64 cuts67848 = true := by
 decide +kernel
def pointBounds67848 : List (Nat × Nat × Nat) := [(8896931840,115430563673552,115430952954082)]
theorem point_links_checked67848 : (cuts67848.take 1).map (fun c => (8896905217-1+2*2^10*c.k,115430527417151+c.lower,115430916697661+c.upper)) = pointBounds67848 := by
 decide +kernel
def cuts67849 : List PrefixCut := [⟨64,183999007,183999115⟩]
theorem checked67849 : checkPrefixCuts (2^48) 8897036289 10 Manual.Count131072.C067849.packed 64 cuts67849 = true := by
 decide +kernel
def cuts67850 : List PrefixCut := [⟨21,58274224,58274255⟩,
⟨64,179725408,179725508⟩]
theorem checked67850 : checkPrefixCuts (2^48) 8897167361 10 Manual.Count131072.C067850.packed 64 cuts67850 = true := by
 decide +kernel
def pointBounds67850 : List (Nat × Nat × Nat) := [(8897210368,115430950718220,115431339998976)]
theorem point_links_checked67850 : (cuts67850.take 1).map (fun c => (8897167361-1+2*2^10*c.k,115430892443996+c.lower,115431281724721+c.upper)) = pointBounds67850 := by
 decide +kernel
def cuts67851 : List PrefixCut := [⟨64,181842364,181842471⟩]
theorem checked67851 : checkPrefixCuts (2^48) 8897298433 10 Manual.Count131072.C067851.packed 64 cuts67851 = true := by
 decide +kernel
def cuts67852 : List PrefixCut := [⟨29,81556120,81556172⟩,
⟨64,181112062,181112177⟩]
theorem checked67852 : checkPrefixCuts (2^48) 8897429505 10 Manual.Count131072.C067852.packed 64 cuts67852 = true := by
 decide +kernel
def pointBounds67852 : List (Nat × Nat × Nat) := [(8897488896,115431335567888,115431724848872)]
theorem point_links_checked67852 : (cuts67852.take 1).map (fun c => (8897429505-1+2*2^10*c.k,115431254011768+c.lower,115431643292700+c.upper)) = pointBounds67852 := by
 decide +kernel
def cuts67853 : List PrefixCut := [⟨64,180223632,180223738⟩]
theorem checked67853 : checkPrefixCuts (2^48) 8897560577 10 Manual.Count131072.C067853.packed 64 cuts67853 = true := by
 decide +kernel
def cuts67854 : List PrefixCut := [⟨37,104646804,104646864⟩,
⟨64,182941522,182941628⟩]
theorem checked67854 : checkPrefixCuts (2^48) 8897691649 10 Manual.Count131072.C067854.packed 64 cuts67854 = true := by
 decide +kernel
def pointBounds67854 : List (Nat × Nat × Nat) := [(8897767424,115431719994266,115432109275479)]
theorem point_links_checked67854 : (cuts67854.take 1).map (fun c => (8897691649-1+2*2^10*c.k,115431615347462+c.lower,115432004628615+c.upper)) = pointBounds67854 := by
 decide +kernel
def cuts67855 : List PrefixCut := [⟨64,180724466,180724566⟩]
theorem checked67855 : checkPrefixCuts (2^48) 8897822721 10 Manual.Count131072.C067855.packed 64 cuts67855 = true := by
 decide +kernel
def cuts67856 : List PrefixCut := [⟨45,125331941,125332014⟩,
⟨64,179994234,179994337⟩]
theorem checked67856 : checkPrefixCuts (2^48) 8897953793 10 Manual.Count131072.C067856.packed 64 cuts67856 = true := by
 decide +kernel
def pointBounds67856 : List (Nat × Nat × Nat) := [(8898045952,115432104345391,115432493626823)]
theorem point_links_checked67856 : (cuts67856.take 1).map (fun c => (8897953793-1+2*2^10*c.k,115431979013450+c.lower,115432368294809+c.upper)) = pointBounds67856 := by
 decide +kernel
def cuts67857 : List PrefixCut := [⟨64,180339551,180339644⟩]
theorem checked67857 : checkPrefixCuts (2^48) 8898084865 10 Manual.Count131072.C067857.packed 64 cuts67857 = true := by
 decide +kernel
def cuts67858 : List PrefixCut := [⟨53,150317836,150317922⟩,
⟨64,181222601,181222703⟩]
theorem checked67858 : checkPrefixCuts (2^48) 8898215937 10 Manual.Count131072.C067858.packed 64 cuts67858 = true := by
 decide +kernel
def pointBounds67858 : List (Nat × Nat × Nat) := [(8898324480,115432489665071,115432878946712)]
theorem point_links_checked67858 : (cuts67858.take 1).map (fun c => (8898215937-1+2*2^10*c.k,115432339347235+c.lower,115432728628790+c.upper)) = pointBounds67858 := by
 decide +kernel
def cuts67859 : List PrefixCut := [⟨64,179764846,179764957⟩]
theorem checked67859 : checkPrefixCuts (2^48) 8898347009 10 Manual.Count131072.C067859.packed 64 cuts67859 = true := by
 decide +kernel
def cuts67860 : List PrefixCut := [⟨61,172107421,172107528⟩,
⟨64,180458097,180458208⟩]
theorem checked67860 : checkPrefixCuts (2^48) 8898478081 10 Manual.Count131072.C067860.packed 64 cuts67860 = true := by
 decide +kernel
def pointBounds67860 : List (Nat × Nat × Nat) := [(8898603008,115432872442103,115433261723978)]
theorem point_links_checked67860 : (cuts67860.take 1).map (fun c => (8898478081-1+2*2^10*c.k,115432700334682+c.lower,115433089616450+c.upper)) = pointBounds67860 := by
 decide +kernel
def cuts67861 : List PrefixCut := [⟨64,179664661,179664764⟩]
theorem checked67861 : checkPrefixCuts (2^48) 8898609153 10 Manual.Count131072.C067861.packed 64 cuts67861 = true := by
 decide +kernel
def cuts67862 : List PrefixCut := [⟨64,180674194,180674297⟩]
theorem checked67862 : checkPrefixCuts (2^48) 8898740225 10 Manual.Count131072.C067862.packed 64 cuts67862 = true := by
 decide +kernel
def cuts67863 : List PrefixCut := [⟨5,14455086,14455095⟩,
⟨64,182000002,182000110⟩]
theorem checked67863 : checkPrefixCuts (2^48) 8898871297 10 Manual.Count131072.C067863.packed 64 cuts67863 = true := by
 decide +kernel
def pointBounds67863 : List (Nat × Nat × Nat) := [(8898881536,115433255586720,115433644868814)]
theorem point_links_checked67863 : (cuts67863.take 1).map (fun c => (8898871297-1+2*2^10*c.k,115433241131634+c.lower,115433630413719+c.upper)) = pointBounds67863 := by
 decide +kernel
def cuts67864 : List PrefixCut := [⟨64,180953528,180953630⟩]
theorem checked67864 : checkPrefixCuts (2^48) 8899002369 10 Manual.Count131072.C067864.packed 64 cuts67864 = true := by
 decide +kernel
def cuts67865 : List PrefixCut := [⟨13,38809307,38809327⟩,
⟨64,184683138,184683244⟩]
theorem checked67865 : checkPrefixCuts (2^48) 8899133441 10 Manual.Count131072.C067865.packed 64 cuts67865 = true := by
 decide +kernel
def pointBounds67865 : List (Nat × Nat × Nat) := [(8899160064,115433642894471,115434032176786)]
theorem point_links_checked67865 : (cuts67865.take 1).map (fun c => (8899133441-1+2*2^10*c.k,115433604085164+c.lower,115433993367459+c.upper)) = pointBounds67865 := by
 decide +kernel
def cuts67866 : List PrefixCut := [⟨64,178892350,178892454⟩]
theorem checked67866 : checkPrefixCuts (2^48) 8899264513 10 Manual.Count131072.C067866.packed 64 cuts67866 = true := by
 decide +kernel
def cuts67867 : List PrefixCut := [⟨21,59208482,59208518⟩,
⟨64,178984594,178984708⟩]
theorem checked67867 : checkPrefixCuts (2^48) 8899395585 10 Manual.Count131072.C067867.packed 64 cuts67867 = true := by
 decide +kernel
def pointBounds67867 : List (Nat × Nat × Nat) := [(8899438592,115434026869134,115434416151675)]
theorem point_links_checked67867 : (cuts67867.take 1).map (fun c => (8899395585-1+2*2^10*c.k,115433967660652+c.lower,115434356943157+c.upper)) = pointBounds67867 := by
 decide +kernel
def cuts67868 : List PrefixCut := [⟨64,183694527,183694634⟩]
theorem checked67868 : checkPrefixCuts (2^48) 8899526657 10 Manual.Count131072.C067868.packed 64 cuts67868 = true := by
 decide +kernel
def cuts67869 : List PrefixCut := [⟨29,82294767,82294814⟩,
⟨64,182458335,182458440⟩]
theorem checked67869 : checkPrefixCuts (2^48) 8899657729 10 Manual.Count131072.C067869.packed 64 cuts67869 = true := by
 decide +kernel
def pointBounds67869 : List (Nat × Nat × Nat) := [(8899717120,115434412634540,115434801917313)]
theorem point_links_checked67869 : (cuts67869.take 1).map (fun c => (8899657729-1+2*2^10*c.k,115434330339773+c.lower,115434719622499+c.upper)) = pointBounds67869 := by
 decide +kernel
def cuts67870 : List PrefixCut := [⟨64,180494773,180494877⟩]
theorem checked67870 : checkPrefixCuts (2^48) 8899788801 10 Manual.Count131072.C067870.packed 64 cuts67870 = true := by
 decide +kernel
def cuts67871 : List PrefixCut := [⟨37,105221512,105221573⟩,
⟨64,181535797,181535901⟩]
theorem checked67871 : checkPrefixCuts (2^48) 8899919873 10 Manual.Count131072.C067871.packed 64 cuts67871 = true := by
 decide +kernel
def pointBounds67871 : List (Nat × Nat × Nat) := [(8899995648,115434798514393,115435187797389)]
theorem point_links_checked67871 : (cuts67871.take 1).map (fun c => (8899919873-1+2*2^10*c.k,115434693292881+c.lower,115435082575816+c.upper)) = pointBounds67871 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000245
