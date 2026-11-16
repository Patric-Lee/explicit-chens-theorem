import PlattAssemblyKernel
import PlattCertificates.Count131072.C052016
import PlattCertificates.Count131072.C052017
import PlattCertificates.Count131072.C052018
import PlattCertificates.Count131072.C052019
import PlattCertificates.Count131072.C052020
import PlattCertificates.Count131072.C052021
import PlattCertificates.Count131072.C052022
import PlattCertificates.Count131072.C052023
import PlattCertificates.Count131072.C052024
import PlattCertificates.Count131072.C052025
import PlattCertificates.Count131072.C052026
import PlattCertificates.Count131072.C052027
import PlattCertificates.Count131072.C052028
import PlattCertificates.Count131072.C052029
import PlattCertificates.Count131072.C052030
import PlattCertificates.Count131072.C052031
import PlattCertificates.Count131072.C052032
import PlattCertificates.Count131072.C052033
import PlattCertificates.Count131072.C052034
import PlattCertificates.Count131072.C052035
import PlattCertificates.Count131072.C052036
import PlattCertificates.Count131072.C052037
import PlattCertificates.Count131072.C052038
import PlattCertificates.Count131072.C052039
import PlattCertificates.Count131072.C052040
import PlattCertificates.Count131072.C052041
import PlattCertificates.Count131072.C052042
import PlattCertificates.Count131072.C052043
import PlattCertificates.Count131072.C052044
import PlattCertificates.Count131072.C052045
import PlattCertificates.Count131072.C052046
import PlattCertificates.Count131072.C052047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52016 : List PrefixCut := [⟨15,56651569,56651600⟩,
⟨64,240550785,240550920⟩]
theorem checked52016 : checkPrefixCuts (2^48) 6821773313 10 Manual.Count131072.C052016.packed 64 cuts52016 = true := by
 decide +kernel
def pointBounds52016 : List (Nat × Nat × Nat) := [(6821804032,112148441811704,112148829213280)]
theorem point_links_checked52016 : (cuts52016.take 1).map (fun c => (6821773313-1+2*2^10*c.k,112148385160135+c.lower,112148772561680+c.upper)) = pointBounds52016 := by
 decide +kernel
def cuts52017 : List PrefixCut := [⟨56,209353792,209353912⟩,
⟨64,239143305,239143442⟩]
theorem checked52017 : checkPrefixCuts (2^48) 6821904385 10 Manual.Count131072.C052017.packed 64 cuts52017 = true := by
 decide +kernel
def pointBounds52017 : List (Nat × Nat × Nat) := [(6822019072,112148835064712,112149222466512)]
theorem point_links_checked52017 : (cuts52017.take 1).map (fun c => (6821904385-1+2*2^10*c.k,112148625710920+c.lower,112149013112600+c.upper)) = pointBounds52017 := by
 decide +kernel
def cuts52018 : List PrefixCut := [⟨64,238561068,238561205⟩]
theorem checked52018 : checkPrefixCuts (2^48) 6822035457 10 Manual.Count131072.C052018.packed 64 cuts52018 = true := by
 decide +kernel
def cuts52019 : List PrefixCut := [⟨33,124436141,124436211⟩,
⟨64,241238296,241238433⟩]
theorem checked52019 : checkPrefixCuts (2^48) 6822166529 10 Manual.Count131072.C052019.packed 64 cuts52019 = true := by
 decide +kernel
def pointBounds52019 : List (Nat × Nat × Nat) := [(6822234112,112149227851434,112149615253458)]
theorem point_links_checked52019 : (cuts52019.take 1).map (fun c => (6822166529-1+2*2^10*c.k,112149103415293+c.lower,112149490817247+c.upper)) = pointBounds52019 := by
 decide +kernel
def cuts52020 : List PrefixCut := [⟨64,237603002,237603134⟩]
theorem checked52020 : checkPrefixCuts (2^48) 6822297601 10 Manual.Count131072.C052020.packed 64 cuts52020 = true := by
 decide +kernel
def cuts52021 : List PrefixCut := [⟨10,36677673,36677694⟩,
⟨64,239124931,239125072⟩]
theorem checked52021 : checkPrefixCuts (2^48) 6822428673 10 Manual.Count131072.C052021.packed 64 cuts52021 = true := by
 decide +kernel
def pointBounds52021 : List (Nat × Nat × Nat) := [(6822449152,112149618934264,112150006336508)]
theorem point_links_checked52021 : (cuts52021.take 1).map (fun c => (6822428673-1+2*2^10*c.k,112149582256591+c.lower,112149969658814+c.upper)) = pointBounds52021 := by
 decide +kernel
def cuts52022 : List PrefixCut := [⟨51,189035813,189035922⟩,
⟨64,238088941,238089077⟩]
theorem checked52022 : checkPrefixCuts (2^48) 6822559745 10 Manual.Count131072.C052022.packed 64 cuts52022 = true := by
 decide +kernel
def pointBounds52022 : List (Nat × Nat × Nat) := [(6822664192,112150010417335,112150397819808)]
theorem point_links_checked52022 : (cuts52022.take 1).map (fun c => (6822559745-1+2*2^10*c.k,112149821381522+c.lower,112150208783886+c.upper)) = pointBounds52022 := by
 decide +kernel
def cuts52023 : List PrefixCut := [⟨64,236929209,236929343⟩]
theorem checked52023 : checkPrefixCuts (2^48) 6822690817 10 Manual.Count131072.C052023.packed 64 cuts52023 = true := by
 decide +kernel
def cuts52024 : List PrefixCut := [⟨28,103054328,103054385⟩,
⟨64,240224994,240225130⟩]
theorem checked52024 : checkPrefixCuts (2^48) 6822821889 10 Manual.Count131072.C052024.packed 64 cuts52024 = true := by
 decide +kernel
def pointBounds52024 : List (Nat × Nat × Nat) := [(6822879232,112150399454000,112150786856691)]
theorem point_links_checked52024 : (cuts52024.take 1).map (fun c => (6822821889-1+2*2^10*c.k,112150296399672+c.lower,112150683802306+c.upper)) = pointBounds52024 := by
 decide +kernel
def cuts52025 : List PrefixCut := [⟨64,238322750,238322884⟩]
theorem checked52025 : checkPrefixCuts (2^48) 6822952961 10 Manual.Count131072.C052025.packed 64 cuts52025 = true := by
 decide +kernel
def cuts52026 : List PrefixCut := [⟨5,19471555,19471566⟩,
⟨64,239679532,239679667⟩]
theorem checked52026 : checkPrefixCuts (2^48) 6823084033 10 Manual.Count131072.C052026.packed 64 cuts52026 = true := by
 decide +kernel
def pointBounds52026 : List (Nat × Nat × Nat) := [(6823094272,112150794418971,112151181821886)]
theorem point_links_checked52026 : (cuts52026.take 1).map (fun c => (6823084033-1+2*2^10*c.k,112150774947416+c.lower,112151162350320+c.upper)) = pointBounds52026 := by
 decide +kernel
def cuts52027 : List PrefixCut := [⟨46,172558157,172558255⟩,
⟨64,237859835,237859971⟩]
theorem checked52027 : checkPrefixCuts (2^48) 6823215105 10 Manual.Count131072.C052027.packed 64 cuts52027 = true := by
 decide +kernel
def pointBounds52027 : List (Nat × Nat × Nat) := [(6823309312,112151187185105,112151574588242)]
theorem point_links_checked52027 : (cuts52027.take 1).map (fun c => (6823215105-1+2*2^10*c.k,112151014626948+c.lower,112151402029987+c.upper)) = pointBounds52027 := by
 decide +kernel
def cuts52028 : List PrefixCut := [⟨64,242970427,242970563⟩]
theorem checked52028 : checkPrefixCuts (2^48) 6823346177 10 Manual.Count131072.C052028.packed 64 cuts52028 = true := by
 decide +kernel
def cuts52029 : List PrefixCut := [⟨23,85925424,85925473⟩,
⟨64,240284449,240284587⟩]
theorem checked52029 : checkPrefixCuts (2^48) 6823477249 10 Manual.Count131072.C052029.packed 64 cuts52029 = true := by
 decide +kernel
def pointBounds52029 : List (Nat × Nat × Nat) := [(6823524352,112151581382634,112151968785994)]
theorem point_links_checked52029 : (cuts52029.take 1).map (fun c => (6823477249-1+2*2^10*c.k,112151495457210+c.lower,112151882860521+c.upper)) = pointBounds52029 := by
 decide +kernel
def cuts52030 : List PrefixCut := [⟨64,236732356,236732491⟩]
theorem checked52030 : checkPrefixCuts (2^48) 6823608321 10 Manual.Count131072.C052030.packed 64 cuts52030 = true := by
 decide +kernel
def pointBounds52030 : List (Nat × Nat × Nat) := [(6823739392,112151972474015,112152359877599)]
theorem point_links_checked52030 : (cuts52030.take 1).map (fun c => (6823608321-1+2*2^10*c.k,112151735741659+c.lower,112152123145108+c.upper)) = pointBounds52030 := by
 decide +kernel
def cuts52031 : List PrefixCut := [⟨64,238006517,238006652⟩]
theorem checked52031 : checkPrefixCuts (2^48) 6823739393 10 Manual.Count131072.C052031.packed 64 cuts52031 = true := by
 decide +kernel
def cuts52032 : List PrefixCut := [⟨41,150020138,150020224⟩,
⟨64,234660871,234661004⟩]
theorem checked52032 : checkPrefixCuts (2^48) 6823870465 10 Manual.Count131072.C052032.packed 64 cuts52032 = true := by
 decide +kernel
def pointBounds52032 : List (Nat × Nat × Nat) := [(6823954432,112152360500670,112152747904475)]
theorem point_links_checked52032 : (cuts52032.take 1).map (fun c => (6823870465-1+2*2^10*c.k,112152210480532+c.lower,112152597884251+c.upper)) = pointBounds52032 := by
 decide +kernel
def cuts52033 : List PrefixCut := [⟨64,237461171,237461308⟩]
theorem checked52033 : checkPrefixCuts (2^48) 6824001537 10 Manual.Count131072.C052033.packed 64 cuts52033 = true := by
 decide +kernel
def cuts52034 : List PrefixCut := [⟨18,67314898,67314936⟩,
⟨64,240220134,240220272⟩]
theorem checked52034 : checkPrefixCuts (2^48) 6824132609 10 Manual.Count131072.C052034.packed 64 cuts52034 = true := by
 decide +kernel
def pointBounds52034 : List (Nat × Nat × Nat) := [(6824169472,112152749917472,112153137321499)]
theorem point_links_checked52034 : (cuts52034.take 1).map (fun c => (6824132609-1+2*2^10*c.k,112152682602574+c.lower,112153070006563+c.upper)) = pointBounds52034 := by
 decide +kernel
def cuts52035 : List PrefixCut := [⟨59,216128156,216128277⟩,
⟨64,234482373,234482505⟩]
theorem checked52035 : checkPrefixCuts (2^48) 6824263681 10 Manual.Count131072.C052035.packed 64 cuts52035 = true := by
 decide +kernel
def pointBounds52035 : List (Nat × Nat × Nat) := [(6824384512,112153138950864,112153526355112)]
theorem point_links_checked52035 : (cuts52035.take 1).map (fun c => (6824263681-1+2*2^10*c.k,112152922822708+c.lower,112153310226835+c.upper)) = pointBounds52035 := by
 decide +kernel
def cuts52036 : List PrefixCut := [⟨64,239880955,239881088⟩]
theorem checked52036 : checkPrefixCuts (2^48) 6824394753 10 Manual.Count131072.C052036.packed 64 cuts52036 = true := by
 decide +kernel
def cuts52037 : List PrefixCut := [⟨36,132476965,132477041⟩,
⟨64,235463202,235463337⟩]
theorem checked52037 : checkPrefixCuts (2^48) 6824525825 10 Manual.Count131072.C052037.packed 64 cuts52037 = true := by
 decide +kernel
def pointBounds52037 : List (Nat × Nat × Nat) := [(6824599552,112153529663001,112153917067469)]
theorem point_links_checked52037 : (cuts52037.take 1).map (fun c => (6824525825-1+2*2^10*c.k,112153397186036+c.lower,112153784590428+c.upper)) = pointBounds52037 := by
 decide +kernel
def cuts52038 : List PrefixCut := [⟨64,240944052,240944184⟩]
theorem checked52038 : checkPrefixCuts (2^48) 6824656897 10 Manual.Count131072.C052038.packed 64 cuts52038 = true := by
 decide +kernel
def cuts52039 : List PrefixCut := [⟨13,49202831,49202860⟩,
⟨64,239949613,239949751⟩]
theorem checked52039 : checkPrefixCuts (2^48) 6824787969 10 Manual.Count131072.C052039.packed 64 cuts52039 = true := by
 decide +kernel
def pointBounds52039 : List (Nat × Nat × Nat) := [(6824814592,112153922796121,112154310200809)]
theorem point_links_checked52039 : (cuts52039.take 1).map (fun c => (6824787969-1+2*2^10*c.k,112153873593290+c.lower,112154260997949+c.upper)) = pointBounds52039 := by
 decide +kernel
def cuts52040 : List PrefixCut := [⟨54,203281313,203281427⟩,
⟨64,240068732,240068868⟩]
theorem checked52040 : checkPrefixCuts (2^48) 6824919041 10 Manual.Count131072.C052040.packed 64 cuts52040 = true := by
 decide +kernel
def pointBounds52040 : List (Nat × Nat × Nat) := [(6825029632,112154316824216,112154704229127)]
theorem point_links_checked52040 : (cuts52040.take 1).map (fun c => (6824919041-1+2*2^10*c.k,112154113542903+c.lower,112154500947700+c.upper)) = pointBounds52040 := by
 decide +kernel
def cuts52041 : List PrefixCut := [⟨64,237795842,237795981⟩]
theorem checked52041 : checkPrefixCuts (2^48) 6825050113 10 Manual.Count131072.C052041.packed 64 cuts52041 = true := by
 decide +kernel
def cuts52042 : List PrefixCut := [⟨31,115926922,115926991⟩,
⟨64,237873779,237873916⟩]
theorem checked52042 : checkPrefixCuts (2^48) 6825181185 10 Manual.Count131072.C052042.packed 64 cuts52042 = true := by
 decide +kernel
def pointBounds52042 : List (Nat × Nat × Nat) := [(6825244672,112154707334399,112155094739540)]
theorem point_links_checked52042 : (cuts52042.take 1).map (fun c => (6825181185-1+2*2^10*c.k,112154591407477+c.lower,112154978812549+c.upper)) = pointBounds52042 := by
 decide +kernel
def cuts52043 : List PrefixCut := [⟨64,239683743,239683877⟩]
theorem checked52043 : checkPrefixCuts (2^48) 6825312257 10 Manual.Count131072.C052043.packed 64 cuts52043 = true := by
 decide +kernel
def cuts52044 : List PrefixCut := [⟨8,30063243,30063260⟩,
⟨64,239637896,239638036⟩]
theorem checked52044 : checkPrefixCuts (2^48) 6825443329 10 Manual.Count131072.C052044.packed 64 cuts52044 = true := by
 decide +kernel
def pointBounds52044 : List (Nat × Nat × Nat) := [(6825459712,112155099028242,112155486433602)]
theorem point_links_checked52044 : (cuts52044.take 1).map (fun c => (6825443329-1+2*2^10*c.k,112155068964999+c.lower,112155456370342+c.upper)) = pointBounds52044 := by
 decide +kernel
def cuts52045 : List PrefixCut := [⟨49,181447051,181447156⟩,
⟨64,235427035,235427171⟩]
theorem checked52045 : checkPrefixCuts (2^48) 6825574401 10 Manual.Count131072.C052045.packed 64 cuts52045 = true := by
 decide +kernel
def pointBounds52045 : List (Nat × Nat × Nat) := [(6825674752,112155490049946,112155877455534)]
theorem point_links_checked52045 : (cuts52045.take 1).map (fun c => (6825574401-1+2*2^10*c.k,112155308602895+c.lower,112155696008378+c.upper)) = pointBounds52045 := by
 decide +kernel
def cuts52046 : List PrefixCut := [⟨64,242803947,242804083⟩]
theorem checked52046 : checkPrefixCuts (2^48) 6825705473 10 Manual.Count131072.C052046.packed 64 cuts52046 = true := by
 decide +kernel
def cuts52047 : List PrefixCut := [⟨26,98349123,98349178⟩,
⟨64,242304457,242304596⟩]
theorem checked52047 : checkPrefixCuts (2^48) 6825836545 10 Manual.Count131072.C052047.packed 64 cuts52047 = true := by
 decide +kernel
def pointBounds52047 : List (Nat × Nat × Nat) := [(6825889792,112155885183000,112156272588810)]
theorem point_links_checked52047 : (cuts52047.take 1).map (fun c => (6825836545-1+2*2^10*c.k,112155786833877+c.lower,112156174239632+c.upper)) = pointBounds52047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000063
