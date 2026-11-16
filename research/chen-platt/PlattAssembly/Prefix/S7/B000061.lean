import PlattAssemblyKernel
import PlattCertificates.Count131072.C061952
import PlattCertificates.Count131072.C061953
import PlattCertificates.Count131072.C061954
import PlattCertificates.Count131072.C061955
import PlattCertificates.Count131072.C061956
import PlattCertificates.Count131072.C061957
import PlattCertificates.Count131072.C061958
import PlattCertificates.Count131072.C061959
import PlattCertificates.Count131072.C061960
import PlattCertificates.Count131072.C061961
import PlattCertificates.Count131072.C061962
import PlattCertificates.Count131072.C061963
import PlattCertificates.Count131072.C061964
import PlattCertificates.Count131072.C061965
import PlattCertificates.Count131072.C061966
import PlattCertificates.Count131072.C061967
import PlattCertificates.Count131072.C061968
import PlattCertificates.Count131072.C061969
import PlattCertificates.Count131072.C061970
import PlattCertificates.Count131072.C061971
import PlattCertificates.Count131072.C061972
import PlattCertificates.Count131072.C061973
import PlattCertificates.Count131072.C061974
import PlattCertificates.Count131072.C061975
import PlattCertificates.Count131072.C061976
import PlattCertificates.Count131072.C061977
import PlattCertificates.Count131072.C061978
import PlattCertificates.Count131072.C061979
import PlattCertificates.Count131072.C061980
import PlattCertificates.Count131072.C061981
import PlattCertificates.Count131072.C061982
import PlattCertificates.Count131072.C061983
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61952 : List PrefixCut := [⟨64,199148670,199148779⟩]
theorem checked61952 : checkPrefixCuts (2^48) 8124104705 10 Manual.Count131072.C061952.packed 64 cuts61952 = true := by
 decide +kernel
def cuts61953 : List PrefixCut := [⟨12,36828984,36829007⟩,
⟨64,199838380,199838495⟩]
theorem checked61953 : checkPrefixCuts (2^48) 8124235777 10 Manual.Count131072.C061953.packed 64 cuts61953 = true := by
 decide +kernel
def pointBounds61953 : List (Nat × Nat × Nat) := [(8124260352,114312075054680,114312463688109)]
theorem point_links_checked61953 : (cuts61953.take 1).map (fun c => (8124235777-1+2*2^10*c.k,114312038225696+c.lower,114312426859102+c.upper)) = pointBounds61953 := by
 decide +kernel
def cuts61954 : List PrefixCut := [⟨64,198449330,198449447⟩]
theorem checked61954 : checkPrefixCuts (2^48) 8124366849 10 Manual.Count131072.C061954.packed 64 cuts61954 = true := by
 decide +kernel
def cuts61955 : List PrefixCut := [⟨8,24840588,24840603⟩,
⟨64,197337498,197337606⟩]
theorem checked61955 : checkPrefixCuts (2^48) 8124497921 10 Manual.Count131072.C061955.packed 64 cuts61955 = true := by
 decide +kernel
def pointBounds61955 : List (Nat × Nat × Nat) := [(8124514304,114312461353994,114312849987647)]
theorem point_links_checked61955 : (cuts61955.take 1).map (fun c => (8124497921-1+2*2^10*c.k,114312436513406+c.lower,114312825147044+c.upper)) = pointBounds61955 := by
 decide +kernel
def cuts61956 : List PrefixCut := [⟨64,199170462,199170582⟩]
theorem checked61956 : checkPrefixCuts (2^48) 8124628993 10 Manual.Count131072.C061956.packed 64 cuts61956 = true := by
 decide +kernel
def cuts61957 : List PrefixCut := [⟨4,12991527,12991534⟩,
⟨64,199479060,199479176⟩]
theorem checked61957 : checkPrefixCuts (2^48) 8124760065 10 Manual.Count131072.C061957.packed 64 cuts61957 = true := by
 decide +kernel
def pointBounds61957 : List (Nat × Nat × Nat) := [(8124768256,114312846012893,114313234646766)]
theorem point_links_checked61957 : (cuts61957.take 1).map (fun c => (8124760065-1+2*2^10*c.k,114312833021366+c.lower,114313221655232+c.upper)) = pointBounds61957 := by
 decide +kernel
def cuts61958 : List PrefixCut := [⟨64,197916892,197917004⟩]
theorem checked61958 : checkPrefixCuts (2^48) 8124891137 10 Manual.Count131072.C061958.packed 64 cuts61958 = true := by
 decide +kernel
def pointBounds61958 : List (Nat × Nat × Nat) := [(8125022208,114313230417318,114313619051412)]
theorem point_links_checked61958 : (cuts61958.take 1).map (fun c => (8124891137-1+2*2^10*c.k,114313032500426+c.lower,114313421134408+c.upper)) = pointBounds61958 := by
 decide +kernel
def cuts61959 : List PrefixCut := [⟨64,197879058,197879174⟩]
theorem checked61959 : checkPrefixCuts (2^48) 8125022209 10 Manual.Count131072.C061959.packed 64 cuts61959 = true := by
 decide +kernel
def cuts61960 : List PrefixCut := [⟨60,183568748,183568857⟩,
⟨64,196628731,196628848⟩]
theorem checked61960 : checkPrefixCuts (2^48) 8125153281 10 Manual.Count131072.C061960.packed 64 cuts61960 = true := by
 decide +kernel
def pointBounds61960 : List (Nat × Nat × Nat) := [(8125276160,114313611865124,114314000499443)]
theorem point_links_checked61960 : (cuts61960.take 1).map (fun c => (8125153281-1+2*2^10*c.k,114313428296376+c.lower,114313816930586+c.upper)) = pointBounds61960 := by
 decide +kernel
def cuts61961 : List PrefixCut := [⟨64,198080510,198080628⟩]
theorem checked61961 : checkPrefixCuts (2^48) 8125284353 10 Manual.Count131072.C061961.packed 64 cuts61961 = true := by
 decide +kernel
def cuts61962 : List PrefixCut := [⟨56,172027443,172027542⟩,
⟨64,196275980,196276095⟩]
theorem checked61962 : checkPrefixCuts (2^48) 8125415425 10 Manual.Count131072.C061962.packed 64 cuts61962 = true := by
 decide +kernel
def pointBounds61962 : List (Nat × Nat × Nat) := [(8125530112,114313995033060,114314383667604)]
theorem point_links_checked61962 : (cuts61962.take 1).map (fun c => (8125415425-1+2*2^10*c.k,114313823005617+c.lower,114314211640062+c.upper)) = pointBounds61962 := by
 decide +kernel
def cuts61963 : List PrefixCut := [⟨64,198108776,198108889⟩]
theorem checked61963 : checkPrefixCuts (2^48) 8125546497 10 Manual.Count131072.C061963.packed 64 cuts61963 = true := by
 decide +kernel
def cuts61964 : List PrefixCut := [⟨52,162114952,162115050⟩,
⟨64,199733633,199733753⟩]
theorem checked61964 : checkPrefixCuts (2^48) 8125677569 10 Manual.Count131072.C061964.packed 64 cuts61964 = true := by
 decide +kernel
def pointBounds61964 : List (Nat × Nat × Nat) := [(8125784064,114314379505325,114314768140096)]
theorem point_links_checked61964 : (cuts61964.take 1).map (fun c => (8125677569-1+2*2^10*c.k,114314217390373+c.lower,114314606025046+c.upper)) = pointBounds61964 := by
 decide +kernel
def cuts61965 : List PrefixCut := [⟨64,196786074,196786189⟩]
theorem checked61965 : checkPrefixCuts (2^48) 8125808641 10 Manual.Count131072.C061965.packed 64 cuts61965 = true := by
 decide +kernel
def cuts61966 : List PrefixCut := [⟨48,149397341,149397433⟩,
⟨64,199207602,199207722⟩]
theorem checked61966 : checkPrefixCuts (2^48) 8125939713 10 Manual.Count131072.C061966.packed 64 cuts61966 = true := by
 decide +kernel
def pointBounds61966 : List (Nat × Nat × Nat) := [(8126038016,114314763307421,114315151942421)]
theorem point_links_checked61966 : (cuts61966.take 1).map (fun c => (8125939713-1+2*2^10*c.k,114314613910080+c.lower,114315002544988+c.upper)) = pointBounds61966 := by
 decide +kernel
def cuts61967 : List PrefixCut := [⟨64,196225534,196225648⟩]
theorem checked61967 : checkPrefixCuts (2^48) 8126070785 10 Manual.Count131072.C061967.packed 64 cuts61967 = true := by
 decide +kernel
def cuts61968 : List PrefixCut := [⟨44,137130844,137130921⟩,
⟨64,199824664,199824776⟩]
theorem checked61968 : checkPrefixCuts (2^48) 8126201857 10 Manual.Count131072.C061968.packed 64 cuts61968 = true := by
 decide +kernel
def pointBounds61968 : List (Nat × Nat × Nat) := [(8126291968,114315146474060,114315535109279)]
theorem point_links_checked61968 : (cuts61968.take 1).map (fun c => (8126201857-1+2*2^10*c.k,114315009343216+c.lower,114315397978358+c.upper)) = pointBounds61968 := by
 decide +kernel
def cuts61969 : List PrefixCut := [⟨64,202315304,202315417⟩]
theorem checked61969 : checkPrefixCuts (2^48) 8126332929 10 Manual.Count131072.C061969.packed 64 cuts61969 = true := by
 decide +kernel
def cuts61970 : List PrefixCut := [⟨40,124033834,124033906⟩,
⟨64,198155665,198155779⟩]
theorem checked61970 : checkPrefixCuts (2^48) 8126464001 10 Manual.Count131072.C061970.packed 64 cuts61970 = true := by
 decide +kernel
def pointBounds61970 : List (Nat × Nat × Nat) := [(8126545920,114315535517018,114315924152457)]
theorem point_links_checked61970 : (cuts61970.take 1).map (fun c => (8126464001-1+2*2^10*c.k,114315411483184+c.lower,114315800118551+c.upper)) = pointBounds61970 := by
 decide +kernel
def cuts61971 : List PrefixCut := [⟨64,197667576,197667690⟩]
theorem checked61971 : checkPrefixCuts (2^48) 8126595073 10 Manual.Count131072.C061971.packed 64 cuts61971 = true := by
 decide +kernel
def cuts61972 : List PrefixCut := [⟨37,115682724,115682791⟩,
⟨64,200712297,200712414⟩]
theorem checked61972 : checkPrefixCuts (2^48) 8126726145 10 Manual.Count131072.C061972.packed 64 cuts61972 = true := by
 decide +kernel
def pointBounds61972 : List (Nat × Nat × Nat) := [(8126801920,114315922989149,114316311624811)]
theorem point_links_checked61972 : (cuts61972.take 1).map (fun c => (8126726145-1+2*2^10*c.k,114315807306425+c.lower,114316195942020+c.upper)) = pointBounds61972 := by
 decide +kernel
def cuts61973 : List PrefixCut := [⟨64,198007542,198007659⟩]
theorem checked61973 : checkPrefixCuts (2^48) 8126857217 10 Manual.Count131072.C061973.packed 64 cuts61973 = true := by
 decide +kernel
def cuts61974 : List PrefixCut := [⟨34,105046256,105046318⟩,
⟨64,197207759,197207871⟩]
theorem checked61974 : checkPrefixCuts (2^48) 8126988289 10 Manual.Count131072.C061974.packed 64 cuts61974 = true := by
 decide +kernel
def pointBounds61974 : List (Nat × Nat × Nat) := [(8127057920,114316311072520,114316699708411)]
theorem point_links_checked61974 : (cuts61974.take 1).map (fun c => (8126988289-1+2*2^10*c.k,114316206026264+c.lower,114316594662093+c.upper)) = pointBounds61974 := by
 decide +kernel
def cuts61975 : List PrefixCut := [⟨64,201464533,201464649⟩]
theorem checked61975 : checkPrefixCuts (2^48) 8127119361 10 Manual.Count131072.C061975.packed 64 cuts61975 = true := by
 decide +kernel
def cuts61976 : List PrefixCut := [⟨31,97943074,97943129⟩,
⟨64,199798892,199799011⟩]
theorem checked61976 : checkPrefixCuts (2^48) 8127250433 10 Manual.Count131072.C061976.packed 64 cuts61976 = true := by
 decide +kernel
def pointBounds61976 : List (Nat × Nat × Nat) := [(8127313920,114316702641630,114317091277742)]
theorem point_links_checked61976 : (cuts61976.take 1).map (fun c => (8127250433-1+2*2^10*c.k,114316604698556+c.lower,114316993334613+c.upper)) = pointBounds61976 := by
 decide +kernel
def cuts61977 : List PrefixCut := [⟨64,201631205,201631314⟩]
theorem checked61977 : checkPrefixCuts (2^48) 8127381505 10 Manual.Count131072.C061977.packed 64 cuts61977 = true := by
 decide +kernel
def cuts61978 : List PrefixCut := [⟨28,88900940,88900989⟩,
⟨64,203117118,203117230⟩]
theorem checked61978 : checkPrefixCuts (2^48) 8127512577 10 Manual.Count131072.C061978.packed 64 cuts61978 = true := by
 decide +kernel
def pointBounds61978 : List (Nat × Nat × Nat) := [(8127569920,114317095029593,114317483665927)]
theorem point_links_checked61978 : (cuts61978.take 1).map (fun c => (8127512577-1+2*2^10*c.k,114317006128653+c.lower,114317394764938+c.upper)) = pointBounds61978 := by
 decide +kernel
def cuts61979 : List PrefixCut := [⟨64,197676685,197676799⟩]
theorem checked61979 : checkPrefixCuts (2^48) 8127643649 10 Manual.Count131072.C061979.packed 64 cuts61979 = true := by
 decide +kernel
def cuts61980 : List PrefixCut := [⟨25,79097494,79097542⟩,
⟨64,198643177,198643293⟩]
theorem checked61980 : checkPrefixCuts (2^48) 8127774721 10 Manual.Count131072.C061980.packed 64 cuts61980 = true := by
 decide +kernel
def pointBounds61980 : List (Nat × Nat × Nat) := [(8127825920,114317486019950,114317874656509)]
theorem point_links_checked61980 : (cuts61980.take 1).map (fun c => (8127774721-1+2*2^10*c.k,114317406922456+c.lower,114317795558967+c.upper)) = pointBounds61980 := by
 decide +kernel
def cuts61981 : List PrefixCut := [⟨64,198743882,198743990⟩]
theorem checked61981 : checkPrefixCuts (2^48) 8127905793 10 Manual.Count131072.C061981.packed 64 cuts61981 = true := by
 decide +kernel
def cuts61982 : List PrefixCut := [⟨22,67770959,67770996⟩,
⟨64,196939906,196940020⟩]
theorem checked61982 : checkPrefixCuts (2^48) 8128036865 10 Manual.Count131072.C061982.packed 64 cuts61982 = true := by
 decide +kernel
def pointBounds61982 : List (Nat × Nat × Nat) := [(8128081920,114317872080474,114318260717246)]
theorem point_links_checked61982 : (cuts61982.take 1).map (fun c => (8128036865-1+2*2^10*c.k,114317804309515+c.lower,114318192946250+c.upper)) = pointBounds61982 := by
 decide +kernel
def cuts61983 : List PrefixCut := [⟨64,198460435,198460551⟩]
theorem checked61983 : checkPrefixCuts (2^48) 8128167937 10 Manual.Count131072.C061983.packed 64 cuts61983 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000061
