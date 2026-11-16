import PlattAssemblyKernel
import PlattCertificates.Count131072.C055952
import PlattCertificates.Count131072.C055953
import PlattCertificates.Count131072.C055954
import PlattCertificates.Count131072.C055955
import PlattCertificates.Count131072.C055956
import PlattCertificates.Count131072.C055957
import PlattCertificates.Count131072.C055958
import PlattCertificates.Count131072.C055959
import PlattCertificates.Count131072.C055960
import PlattCertificates.Count131072.C055961
import PlattCertificates.Count131072.C055962
import PlattCertificates.Count131072.C055963
import PlattCertificates.Count131072.C055964
import PlattCertificates.Count131072.C055965
import PlattCertificates.Count131072.C055966
import PlattCertificates.Count131072.C055967
import PlattCertificates.Count131072.C055968
import PlattCertificates.Count131072.C055969
import PlattCertificates.Count131072.C055970
import PlattCertificates.Count131072.C055971
import PlattCertificates.Count131072.C055972
import PlattCertificates.Count131072.C055973
import PlattCertificates.Count131072.C055974
import PlattCertificates.Count131072.C055975
import PlattCertificates.Count131072.C055976
import PlattCertificates.Count131072.C055977
import PlattCertificates.Count131072.C055978
import PlattCertificates.Count131072.C055979
import PlattCertificates.Count131072.C055980
import PlattCertificates.Count131072.C055981
import PlattCertificates.Count131072.C055982
import PlattCertificates.Count131072.C055983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000186
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts55952 : List PrefixCut := [⟨64,222218901,222219024⟩]
theorem checked55952 : checkPrefixCuts (2^48) 7337672705 10 Manual.Count131072.C055952.packed 64 cuts55952 = true := by
 decide +kernel
def cuts55953 : List PrefixCut := [⟨41,138822430,138822509⟩,
⟨64,217688525,217688650⟩]
theorem checked55953 : checkPrefixCuts (2^48) 7337803777 10 Manual.Count131072.C055953.packed 64 cuts55953 = true := by
 decide +kernel
def pointBounds55953 : List (Nat × Nat × Nat) := [(7337887744,113053480582876,113053868498415)]
theorem point_links_checked55953 : (cuts55953.take 1).map (fun c => (7337803777-1+2*2^10*c.k,113053341760446+c.lower,113053729675906+c.upper)) = pointBounds55953 := by
 decide +kernel
def cuts55954 : List PrefixCut := [⟨64,220292997,220293128⟩]
theorem checked55954 : checkPrefixCuts (2^48) 7337934849 10 Manual.Count131072.C055954.packed 64 cuts55954 = true := by
 decide +kernel
def cuts55955 : List PrefixCut := [⟨25,86113829,86113878⟩,
⟨64,217834202,217834327⟩]
theorem checked55955 : checkPrefixCuts (2^48) 7338065921 10 Manual.Count131072.C055955.packed 64 cuts55955 = true := by
 decide +kernel
def pointBounds55955 : List (Nat × Nat × Nat) := [(7338117120,113053865855797,113054253771562)]
theorem point_links_checked55955 : (cuts55955.take 1).map (fun c => (7338065921-1+2*2^10*c.k,113053779741968+c.lower,113054167657684+c.upper)) = pointBounds55955 := by
 decide +kernel
def cuts55956 : List PrefixCut := [⟨64,220093365,220093492⟩]
theorem checked55956 : checkPrefixCuts (2^48) 7338196993 10 Manual.Count131072.C055956.packed 64 cuts55956 = true := by
 decide +kernel
def cuts55957 : List PrefixCut := [⟨9,32833395,32833413⟩,
⟨64,225075807,225075932⟩]
theorem checked55957 : checkPrefixCuts (2^48) 7338328065 10 Manual.Count131072.C055957.packed 64 cuts55957 = true := by
 decide +kernel
def pointBounds55957 : List (Nat × Nat × Nat) := [(7338346496,113054250502930,113054638418916)]
theorem point_links_checked55957 : (cuts55957.take 1).map (fun c => (7338328065-1+2*2^10*c.k,113054217669535+c.lower,113054605585503+c.upper)) = pointBounds55957 := by
 decide +kernel
def cuts55958 : List PrefixCut := [⟨57,197839350,197839460⟩,
⟨64,220852639,220852763⟩]
theorem checked55958 : checkPrefixCuts (2^48) 7338459137 10 Manual.Count131072.C055958.packed 64 cuts55958 = true := by
 decide +kernel
def pointBounds55958 : List (Nat × Nat × Nat) := [(7338575872,113054640584692,113055028500895)]
theorem point_links_checked55958 : (cuts55958.take 1).map (fun c => (7338459137-1+2*2^10*c.k,113054442745342+c.lower,113054830661435+c.upper)) = pointBounds55958 := by
 decide +kernel
def cuts55959 : List PrefixCut := [⟨64,220350074,220350202⟩]
theorem checked55959 : checkPrefixCuts (2^48) 7338590209 10 Manual.Count131072.C055959.packed 64 cuts55959 = true := by
 decide +kernel
def cuts55960 : List PrefixCut := [⟨41,144634982,144635066⟩,
⟨64,224258300,224258429⟩]
theorem checked55960 : checkPrefixCuts (2^48) 7338721281 10 Manual.Count131072.C055960.packed 64 cuts55960 = true := by
 decide +kernel
def pointBounds55960 : List (Nat × Nat × Nat) := [(7338805248,113055028583037,113055416499466)]
theorem point_links_checked55960 : (cuts55960.take 1).map (fun c => (7338721281-1+2*2^10*c.k,113054883948055+c.lower,113055271864400+c.upper)) = pointBounds55960 := by
 decide +kernel
def cuts55961 : List PrefixCut := [⟨64,224177582,224177711⟩]
theorem checked55961 : checkPrefixCuts (2^48) 7338852353 10 Manual.Count131072.C055961.packed 64 cuts55961 = true := by
 decide +kernel
def cuts55962 : List PrefixCut := [⟨25,87292018,87292067⟩,
⟨64,222102502,222102630⟩]
theorem checked55962 : checkPrefixCuts (2^48) 7338983425 10 Manual.Count131072.C055962.packed 64 cuts55962 = true := by
 decide +kernel
def pointBounds55962 : List (Nat × Nat × Nat) := [(7339034624,113055419675955,113055807592607)]
theorem point_links_checked55962 : (cuts55962.take 1).map (fun c => (7338983425-1+2*2^10*c.k,113055332383937+c.lower,113055720300540+c.upper)) = pointBounds55962 := by
 decide +kernel
def cuts55963 : List PrefixCut := [⟨64,223440862,223440990⟩]
theorem checked55963 : checkPrefixCuts (2^48) 7339114497 10 Manual.Count131072.C055963.packed 64 cuts55963 = true := by
 decide +kernel
def cuts55964 : List PrefixCut := [⟨9,31486970,31486986⟩,
⟨64,224203900,224204023⟩]
theorem checked55964 : checkPrefixCuts (2^48) 7339245569 10 Manual.Count131072.C055964.packed 64 cuts55964 = true := by
 decide +kernel
def pointBounds55964 : List (Nat × Nat × Nat) := [(7339264000,113055809414271,113056197331146)]
theorem point_links_checked55964 : (cuts55964.take 1).map (fun c => (7339245569-1+2*2^10*c.k,113055777927301+c.lower,113056165844160+c.upper)) = pointBounds55964 := by
 decide +kernel
def cuts55965 : List PrefixCut := [⟨57,196587389,196587505⟩,
⟨64,220441516,220441647⟩]
theorem checked55965 : checkPrefixCuts (2^48) 7339376641 10 Manual.Count131072.C055965.packed 64 cuts55965 = true := by
 decide +kernel
def pointBounds55965 : List (Nat × Nat × Nat) := [(7339493376,113056198718590,113056586635688)]
theorem point_links_checked55965 : (cuts55965.take 1).map (fun c => (7339376641-1+2*2^10*c.k,113056002131201+c.lower,113056390048183+c.upper)) = pointBounds55965 := by
 decide +kernel
def cuts55966 : List PrefixCut := [⟨64,221089515,221089637⟩]
theorem checked55966 : checkPrefixCuts (2^48) 7339507713 10 Manual.Count131072.C055966.packed 64 cuts55966 = true := by
 decide +kernel
def cuts55967 : List PrefixCut := [⟨41,141472215,141472297⟩,
⟨64,221123929,221124056⟩]
theorem checked55967 : checkPrefixCuts (2^48) 7339638785 10 Manual.Count131072.C055967.packed 64 cuts55967 = true := by
 decide +kernel
def pointBounds55967 : List (Nat × Nat × Nat) := [(7339722752,113056585134447,113056973051764)]
theorem point_links_checked55967 : (cuts55967.take 1).map (fun c => (7339638785-1+2*2^10*c.k,113056443662232+c.lower,113056831579467+c.upper)) = pointBounds55967 := by
 decide +kernel
def cuts55968 : List PrefixCut := [⟨64,221580172,221580296⟩]
theorem checked55968 : checkPrefixCuts (2^48) 7339769857 10 Manual.Count131072.C055968.packed 64 cuts55968 = true := by
 decide +kernel
def cuts55969 : List PrefixCut := [⟨25,85938906,85938956⟩,
⟨64,220042277,220042404⟩]
theorem checked55969 : checkPrefixCuts (2^48) 7339900929 10 Manual.Count131072.C055969.packed 64 cuts55969 = true := by
 decide +kernel
def pointBounds55969 : List (Nat × Nat × Nat) := [(7339952128,113056972305239,113057360222775)]
theorem point_links_checked55969 : (cuts55969.take 1).map (fun c => (7339900929-1+2*2^10*c.k,113056886366333+c.lower,113057274283819+c.upper)) = pointBounds55969 := by
 decide +kernel
def cuts55970 : List PrefixCut := [⟨64,219233050,219233172⟩]
theorem checked55970 : checkPrefixCuts (2^48) 7340032001 10 Manual.Count131072.C055970.packed 64 cuts55970 = true := by
 decide +kernel
def cuts55971 : List PrefixCut := [⟨9,30370966,30370984⟩,
⟨64,217005026,217005151⟩]
theorem checked55971 : checkPrefixCuts (2^48) 7340163073 10 Manual.Count131072.C055971.packed 64 cuts55971 = true := by
 decide +kernel
def pointBounds55971 : List (Nat × Nat × Nat) := [(7340181504,113057356012626,113057743930379)]
theorem point_links_checked55971 : (cuts55971.take 1).map (fun c => (7340163073-1+2*2^10*c.k,113057325641660+c.lower,113057713559395+c.upper)) = pointBounds55971 := by
 decide +kernel
def cuts55972 : List PrefixCut := [⟨58,197636477,197636590⟩,
⟨64,218228221,218228345⟩]
theorem checked55972 : checkPrefixCuts (2^48) 7340294145 10 Manual.Count131072.C055972.packed 64 cuts55972 = true := by
 decide +kernel
def pointBounds55972 : List (Nat × Nat × Nat) := [(7340412928,113057740283163,113058128201136)]
theorem point_links_checked55972 : (cuts55972.take 1).map (fun c => (7340294145-1+2*2^10*c.k,113057542646686+c.lower,113057930564546+c.upper)) = pointBounds55972 := by
 decide +kernel
def cuts55973 : List PrefixCut := [⟨64,220831824,220831948⟩]
theorem checked55973 : checkPrefixCuts (2^48) 7340425217 10 Manual.Count131072.C055973.packed 64 cuts55973 = true := by
 decide +kernel
def cuts55974 : List PrefixCut := [⟨43,150235488,150235574⟩,
⟨64,223972150,223972279⟩]
theorem checked55974 : checkPrefixCuts (2^48) 7340556289 10 Manual.Count131072.C055974.packed 64 cuts55974 = true := by
 decide +kernel
def pointBounds55974 : List (Nat × Nat × Nat) := [(7340644352,113058131942219,113058519860413)]
theorem point_links_checked55974 : (cuts55974.take 1).map (fun c => (7340556289-1+2*2^10*c.k,113057981706731+c.lower,113058369624839+c.upper)) = pointBounds55974 := by
 decide +kernel
def cuts55975 : List PrefixCut := [⟨64,222549414,222549541⟩]
theorem checked55975 : checkPrefixCuts (2^48) 7340687361 10 Manual.Count131072.C055975.packed 64 cuts55975 = true := by
 decide +kernel
def cuts55976 : List PrefixCut := [⟨28,96587667,96587721⟩,
⟨64,220359872,220359997⟩]
theorem checked55976 : checkPrefixCuts (2^48) 7340818433 10 Manual.Count131072.C055976.packed 64 cuts55976 = true := by
 decide +kernel
def pointBounds55976 : List (Nat × Nat × Nat) := [(7340875776,113058524815962,113058912734380)]
theorem point_links_checked55976 : (cuts55976.take 1).map (fun c => (7340818433-1+2*2^10*c.k,113058428228295+c.lower,113058816146659+c.upper)) = pointBounds55976 := by
 decide +kernel
def cuts55977 : List PrefixCut := [⟨64,225225476,225225601⟩]
theorem checked55977 : checkPrefixCuts (2^48) 7340949505 10 Manual.Count131072.C055977.packed 64 cuts55977 = true := by
 decide +kernel
def cuts55978 : List PrefixCut := [⟨13,45090620,45090645⟩,
⟨64,221080508,221080634⟩]
theorem checked55978 : checkPrefixCuts (2^48) 7341080577 10 Manual.Count131072.C055978.packed 64 cuts55978 = true := by
 decide +kernel
def pointBounds55978 : List (Nat × Nat × Nat) := [(7341107200,113058918904263,113059306822902)]
theorem point_links_checked55978 : (cuts55978.take 1).map (fun c => (7341080577-1+2*2^10*c.k,113058873813643+c.lower,113059261732257+c.upper)) = pointBounds55978 := by
 decide +kernel
def cuts55979 : List PrefixCut := [⟨62,213983456,213983577⟩,
⟨64,220693144,220693269⟩]
theorem checked55979 : checkPrefixCuts (2^48) 7341211649 10 Manual.Count131072.C055979.packed 64 cuts55979 = true := by
 decide +kernel
def pointBounds55979 : List (Nat × Nat × Nat) := [(7341338624,113059308877607,113059696796468)]
theorem point_links_checked55979 : (cuts55979.take 1).map (fun c => (7341211649-1+2*2^10*c.k,113059094894151+c.lower,113059482812891+c.upper)) = pointBounds55979 := by
 decide +kernel
def cuts55980 : List PrefixCut := [⟨64,220957589,220957714⟩]
theorem checked55980 : checkPrefixCuts (2^48) 7341342721 10 Manual.Count131072.C055980.packed 64 cuts55980 = true := by
 decide +kernel
def cuts55981 : List PrefixCut := [⟨47,162178736,162178828⟩,
⟨64,220761928,220762055⟩]
theorem checked55981 : checkPrefixCuts (2^48) 7341473793 10 Manual.Count131072.C055981.packed 64 cuts55981 = true := by
 decide +kernel
def pointBounds55981 : List (Nat × Nat × Nat) := [(7341570048,113059698723620,113060086642702)]
theorem point_links_checked55981 : (cuts55981.take 1).map (fun c => (7341473793-1+2*2^10*c.k,113059536544884+c.lower,113059924463874+c.upper)) = pointBounds55981 := by
 decide +kernel
def cuts55982 : List PrefixCut := [⟨64,220681317,220681445⟩]
theorem checked55982 : checkPrefixCuts (2^48) 7341604865 10 Manual.Count131072.C055982.packed 64 cuts55982 = true := by
 decide +kernel
def cuts55983 : List PrefixCut := [⟨32,109687416,109687478⟩,
⟨64,218185357,218185481⟩]
theorem checked55983 : checkPrefixCuts (2^48) 7341735937 10 Manual.Count131072.C055983.packed 64 cuts55983 = true := by
 decide +kernel
def pointBounds55983 : List (Nat × Nat × Nat) := [(7341801472,113060087675545,113060475594852)]
theorem point_links_checked55983 : (cuts55983.take 1).map (fun c => (7341735937-1+2*2^10*c.k,113059977988129+c.lower,113060365907374+c.upper)) = pointBounds55983 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000186
