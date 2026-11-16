import PlattAssemblyKernel
import PlattCertificates.Count131072.C060960
import PlattCertificates.Count131072.C060961
import PlattCertificates.Count131072.C060962
import PlattCertificates.Count131072.C060963
import PlattCertificates.Count131072.C060964
import PlattCertificates.Count131072.C060965
import PlattCertificates.Count131072.C060966
import PlattCertificates.Count131072.C060967
import PlattCertificates.Count131072.C060968
import PlattCertificates.Count131072.C060969
import PlattCertificates.Count131072.C060970
import PlattCertificates.Count131072.C060971
import PlattCertificates.Count131072.C060972
import PlattCertificates.Count131072.C060973
import PlattCertificates.Count131072.C060974
import PlattCertificates.Count131072.C060975
import PlattCertificates.Count131072.C060976
import PlattCertificates.Count131072.C060977
import PlattCertificates.Count131072.C060978
import PlattCertificates.Count131072.C060979
import PlattCertificates.Count131072.C060980
import PlattCertificates.Count131072.C060981
import PlattCertificates.Count131072.C060982
import PlattCertificates.Count131072.C060983
import PlattCertificates.Count131072.C060984
import PlattCertificates.Count131072.C060985
import PlattCertificates.Count131072.C060986
import PlattCertificates.Count131072.C060987
import PlattCertificates.Count131072.C060988
import PlattCertificates.Count131072.C060989
import PlattCertificates.Count131072.C060990
import PlattCertificates.Count131072.C060991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60960 : List PrefixCut := [⟨64,201859613,201859730⟩]
theorem checked60960 : checkPrefixCuts (2^48) 7994081281 10 Manual.Count131072.C060960.packed 64 cuts60960 = true := by
 decide +kernel
def cuts60961 : List PrefixCut := [⟨34,108481035,108481094⟩,
⟨64,201891551,201891665⟩]
theorem checked60961 : checkPrefixCuts (2^48) 7994212353 10 Manual.Count131072.C060961.packed 64 cuts60961 = true := by
 decide +kernel
def pointBounds60961 : List (Nat × Nat × Nat) := [(7994281984,114113045271682,114113433791074)]
theorem point_links_checked60961 : (cuts60961.take 1).map (fun c => (7994212353-1+2*2^10*c.k,114112936790647+c.lower,114113325309980+c.upper)) = pointBounds60961 := by
 decide +kernel
def cuts60962 : List PrefixCut := [⟨64,199529215,199529331⟩]
theorem checked60962 : checkPrefixCuts (2^48) 7994343425 10 Manual.Count131072.C060962.packed 64 cuts60962 = true := by
 decide +kernel
def cuts60963 : List PrefixCut := [⟨28,91014114,91014166⟩,
⟨64,205793064,205793180⟩]
theorem checked60963 : checkPrefixCuts (2^48) 7994474497 10 Manual.Count131072.C060963.packed 64 cuts60963 = true := by
 decide +kernel
def pointBounds60963 : List (Nat × Nat × Nat) := [(7994531840,114113429225527,114113817745142)]
theorem point_links_checked60963 : (cuts60963.take 1).map (fun c => (7994474497-1+2*2^10*c.k,114113338211413+c.lower,114113726730976+c.upper)) = pointBounds60963 := by
 decide +kernel
def cuts60964 : List PrefixCut := [⟨64,200508511,200508628⟩]
theorem checked60964 : checkPrefixCuts (2^48) 7994605569 10 Manual.Count131072.C060964.packed 64 cuts60964 = true := by
 decide +kernel
def cuts60965 : List PrefixCut := [⟨22,68443237,68443277⟩,
⟨64,201596634,201596750⟩]
theorem checked60965 : checkPrefixCuts (2^48) 7994736641 10 Manual.Count131072.C060965.packed 64 cuts60965 = true := by
 decide +kernel
def pointBounds60965 : List (Nat × Nat × Nat) := [(7994781696,114113812956225,114114201476061)]
theorem point_links_checked60965 : (cuts60965.take 1).map (fun c => (7994736641-1+2*2^10*c.k,114113744512988+c.lower,114114133032784+c.upper)) = pointBounds60965 := by
 decide +kernel
def cuts60966 : List PrefixCut := [⟨64,200607541,200607654⟩]
theorem checked60966 : checkPrefixCuts (2^48) 7994867713 10 Manual.Count131072.C060966.packed 64 cuts60966 = true := by
 decide +kernel
def cuts60967 : List PrefixCut := [⟨16,50415419,50415449⟩,
⟨64,201942083,201942197⟩]
theorem checked60967 : checkPrefixCuts (2^48) 7994998785 10 Manual.Count131072.C060967.packed 64 cuts60967 = true := by
 decide +kernel
def pointBounds60967 : List (Nat × Nat × Nat) := [(7995031552,114114197132582,114114585652637)]
theorem point_links_checked60967 : (cuts60967.take 1).map (fun c => (7994998785-1+2*2^10*c.k,114114146717163+c.lower,114114535237188+c.upper)) = pointBounds60967 := by
 decide +kernel
def cuts60968 : List PrefixCut := [⟨64,201621925,201622045⟩]
theorem checked60968 : checkPrefixCuts (2^48) 7995129857 10 Manual.Count131072.C060968.packed 64 cuts60968 = true := by
 decide +kernel
def cuts60969 : List PrefixCut := [⟨10,32247939,32247957⟩,
⟨64,204012566,204012683⟩]
theorem checked60969 : checkPrefixCuts (2^48) 7995260929 10 Manual.Count131072.C060969.packed 64 cuts60969 = true := by
 decide +kernel
def pointBounds60969 : List (Nat × Nat × Nat) := [(7995281408,114114582529110,114114971049387)]
theorem point_links_checked60969 : (cuts60969.take 1).map (fun c => (7995260929-1+2*2^10*c.k,114114550281171+c.lower,114114938801430+c.upper)) = pointBounds60969 := by
 decide +kernel
def cuts60970 : List PrefixCut := [⟨64,202213788,202213908⟩]
theorem checked60970 : checkPrefixCuts (2^48) 7995392001 10 Manual.Count131072.C060970.packed 64 cuts60970 = true := by
 decide +kernel
def cuts60971 : List PrefixCut := [⟨4,11652538,11652545⟩,
⟨64,201788021,201788135⟩]
theorem checked60971 : checkPrefixCuts (2^48) 7995523073 10 Manual.Count131072.C060971.packed 64 cuts60971 = true := by
 decide +kernel
def pointBounds60971 : List (Nat × Nat × Nat) := [(7995531264,114114968160063,114115356680566)]
theorem point_links_checked60971 : (cuts60971.take 1).map (fun c => (7995523073-1+2*2^10*c.k,114114956507525+c.lower,114115345028021+c.upper)) = pointBounds60971 := by
 decide +kernel
def cuts60972 : List PrefixCut := [⟨63,201080698,201080813⟩,
⟨64,204037743,204037859⟩]
theorem checked60972 : checkPrefixCuts (2^48) 7995654145 10 Manual.Count131072.C060972.packed 64 cuts60972 = true := by
 decide +kernel
def pointBounds60972 : List (Nat × Nat × Nat) := [(7995783168,114115359376244,114115747896969)]
theorem point_links_checked60972 : (cuts60972.take 1).map (fun c => (7995654145-1+2*2^10*c.k,114115158295546+c.lower,114115546816156+c.upper)) = pointBounds60972 := by
 decide +kernel
def cuts60973 : List PrefixCut := [⟨64,204879252,204879369⟩]
theorem checked60973 : checkPrefixCuts (2^48) 7995785217 10 Manual.Count131072.C060973.packed 64 cuts60973 = true := by
 decide +kernel
def cuts60974 : List PrefixCut := [⟨58,184599641,184599749⟩,
⟨64,203749411,203749530⟩]
theorem checked60974 : checkPrefixCuts (2^48) 7995916289 10 Manual.Count131072.C060974.packed 64 cuts60974 = true := by
 decide +kernel
def pointBounds60974 : List (Nat × Nat × Nat) := [(7996035072,114115751812182,114116140333133)]
theorem point_links_checked60974 : (cuts60974.take 1).map (fun c => (7995916289-1+2*2^10*c.k,114115567212541+c.lower,114115955733384+c.upper)) = pointBounds60974 := by
 decide +kernel
def cuts60975 : List PrefixCut := [⟨64,199205090,199205206⟩]
theorem checked60975 : checkPrefixCuts (2^48) 7996047361 10 Manual.Count131072.C060975.packed 64 cuts60975 = true := by
 decide +kernel
def cuts60976 : List PrefixCut := [⟨53,167732467,167732562⟩,
⟨64,203038719,203038836⟩]
theorem checked60976 : checkPrefixCuts (2^48) 7996178433 10 Manual.Count131072.C060976.packed 64 cuts60976 = true := by
 decide +kernel
def pointBounds60976 : List (Nat × Nat × Nat) := [(7996286976,114116137899509,114116526420682)]
theorem point_links_checked60976 : (cuts60976.take 1).map (fun c => (7996178433-1+2*2^10*c.k,114115970167042+c.lower,114116358688120+c.upper)) = pointBounds60976 := by
 decide +kernel
def cuts60977 : List PrefixCut := [⟨64,201310586,201310703⟩]
theorem checked60977 : checkPrefixCuts (2^48) 7996309505 10 Manual.Count131072.C060977.packed 64 cuts60977 = true := by
 decide +kernel
def cuts60978 : List PrefixCut := [⟨48,153330362,153330448⟩,
⟨64,202433689,202433801⟩]
theorem checked60978 : checkPrefixCuts (2^48) 7996440577 10 Manual.Count131072.C060978.packed 64 cuts60978 = true := by
 decide +kernel
def pointBounds60978 : List (Nat × Nat × Nat) := [(7996538880,114116527846709,114116916368107)]
theorem point_links_checked60978 : (cuts60978.take 1).map (fun c => (7996440577-1+2*2^10*c.k,114116374516347+c.lower,114116763037659+c.upper)) = pointBounds60978 := by
 decide +kernel
def cuts60979 : List PrefixCut := [⟨64,203275147,203275268⟩]
theorem checked60979 : checkPrefixCuts (2^48) 7996571649 10 Manual.Count131072.C060979.packed 64 cuts60979 = true := by
 decide +kernel
def cuts60980 : List PrefixCut := [⟨43,132734204,132734283⟩,
⟨64,198132804,198132923⟩]
theorem checked60980 : checkPrefixCuts (2^48) 7996702721 10 Manual.Count131072.C060980.packed 64 cuts60980 = true := by
 decide +kernel
def pointBounds60980 : List (Nat × Nat × Nat) := [(7996790784,114116912959387,114117301481011)]
theorem point_links_checked60980 : (cuts60980.take 1).map (fun c => (7996702721-1+2*2^10*c.k,114116780225183+c.lower,114117168746728+c.upper)) = pointBounds60980 := by
 decide +kernel
def cuts60981 : List PrefixCut := [⟨64,202881294,202881414⟩]
theorem checked60981 : checkPrefixCuts (2^48) 7996833793 10 Manual.Count131072.C060981.packed 64 cuts60981 = true := by
 decide +kernel
def cuts60982 : List PrefixCut := [⟨38,118862107,118862181⟩,
⟨64,199499022,199499144⟩]
theorem checked60982 : checkPrefixCuts (2^48) 7996964865 10 Manual.Count131072.C060982.packed 64 cuts60982 = true := by
 decide +kernel
def pointBounds60982 : List (Nat × Nat × Nat) := [(7997042688,114117300101388,114117688623246)]
theorem point_links_checked60982 : (cuts60982.take 1).map (fun c => (7996964865-1+2*2^10*c.k,114117181239281+c.lower,114117569761065+c.upper)) = pointBounds60982 := by
 decide +kernel
def cuts60983 : List PrefixCut := [⟨64,199706934,199707051⟩]
theorem checked60983 : checkPrefixCuts (2^48) 7997095937 10 Manual.Count131072.C060983.packed 64 cuts60983 = true := by
 decide +kernel
def cuts60984 : List PrefixCut := [⟨33,105870813,105870870⟩,
⟨64,204842316,204842428⟩]
theorem checked60984 : checkPrefixCuts (2^48) 7997227009 10 Manual.Count131072.C060984.packed 64 cuts60984 = true := by
 decide +kernel
def pointBounds60984 : List (Nat × Nat × Nat) := [(7997294592,114117686316050,114118074838130)]
theorem point_links_checked60984 : (cuts60984.take 1).map (fun c => (7997227009-1+2*2^10*c.k,114117580445237+c.lower,114117968967260+c.upper)) = pointBounds60984 := by
 decide +kernel
def cuts60985 : List PrefixCut := [⟨64,204135043,204135160⟩]
theorem checked60985 : checkPrefixCuts (2^48) 7997358081 10 Manual.Count131072.C060985.packed 64 cuts60985 = true := by
 decide +kernel
def cuts60986 : List PrefixCut := [⟨28,88445744,88445793⟩,
⟨64,204026101,204026217⟩]
theorem checked60986 : checkPrefixCuts (2^48) 7997489153 10 Manual.Count131072.C060986.packed 64 cuts60986 = true := by
 decide +kernel
def pointBounds60986 : List (Nat × Nat × Nat) := [(7997546496,114118077868340,114118466390641)]
theorem point_links_checked60986 : (cuts60986.take 1).map (fun c => (7997489153-1+2*2^10*c.k,114117989422596+c.lower,114118377944848+c.upper)) = pointBounds60986 := by
 decide +kernel
def cuts60987 : List PrefixCut := [⟨64,200960834,200960954⟩]
theorem checked60987 : checkPrefixCuts (2^48) 7997620225 10 Manual.Count131072.C060987.packed 64 cuts60987 = true := by
 decide +kernel
def cuts60988 : List PrefixCut := [⟨23,74294853,74294895⟩,
⟨64,203421142,203421258⟩]
theorem checked60988 : checkPrefixCuts (2^48) 7997751297 10 Manual.Count131072.C060988.packed 64 cuts60988 = true := by
 decide +kernel
def pointBounds60988 : List (Nat × Nat × Nat) := [(7997798400,114118468704384,114118857226914)]
theorem point_links_checked60988 : (cuts60988.take 1).map (fun c => (7997751297-1+2*2^10*c.k,114118394409531+c.lower,114118782932019+c.upper)) = pointBounds60988 := by
 decide +kernel
def cuts60989 : List PrefixCut := [⟨64,208415246,208415365⟩]
theorem checked60989 : checkPrefixCuts (2^48) 7997882369 10 Manual.Count131072.C060989.packed 64 cuts60989 = true := by
 decide +kernel
def cuts60990 : List PrefixCut := [⟨18,55288239,55288265⟩,
⟨64,201549228,201549335⟩]
theorem checked60990 : checkPrefixCuts (2^48) 7998013441 10 Manual.Count131072.C060990.packed 64 cuts60990 = true := by
 decide +kernel
def pointBounds60990 : List (Nat × Nat × Nat) := [(7998050304,114118861534158,114119250056907)]
theorem point_links_checked60990 : (cuts60990.take 1).map (fun c => (7998013441-1+2*2^10*c.k,114118806245919+c.lower,114119194768642+c.upper)) = pointBounds60990 := by
 decide +kernel
def cuts60991 : List PrefixCut := [⟨64,203270355,203270474⟩]
theorem checked60991 : checkPrefixCuts (2^48) 7998144513 10 Manual.Count131072.C060991.packed 64 cuts60991 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000030
