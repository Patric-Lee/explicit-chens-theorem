import PlattAssemblyKernel
import PlattCertificates.Count131072.C070064
import PlattCertificates.Count131072.C070065
import PlattCertificates.Count131072.C070066
import PlattCertificates.Count131072.C070067
import PlattCertificates.Count131072.C070068
import PlattCertificates.Count131072.C070069
import PlattCertificates.Count131072.C070070
import PlattCertificates.Count131072.C070071
import PlattCertificates.Count131072.C070072
import PlattCertificates.Count131072.C070073
import PlattCertificates.Count131072.C070074
import PlattCertificates.Count131072.C070075
import PlattCertificates.Count131072.C070076
import PlattCertificates.Count131072.C070077
import PlattCertificates.Count131072.C070078
import PlattCertificates.Count131072.C070079
import PlattCertificates.Count131072.C070080
import PlattCertificates.Count131072.C070081
import PlattCertificates.Count131072.C070082
import PlattCertificates.Count131072.C070083
import PlattCertificates.Count131072.C070084
import PlattCertificates.Count131072.C070085
import PlattCertificates.Count131072.C070086
import PlattCertificates.Count131072.C070087
import PlattCertificates.Count131072.C070088
import PlattCertificates.Count131072.C070089
import PlattCertificates.Count131072.C070090
import PlattCertificates.Count131072.C070091
import PlattCertificates.Count131072.C070092
import PlattCertificates.Count131072.C070093
import PlattCertificates.Count131072.C070094
import PlattCertificates.Count131072.C070095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70064 : List PrefixCut := [⟨64,176836583,176836685⟩]
theorem checked70064 : checkPrefixCuts (2^48) 9187360769 10 Manual.Count131072.C070064.packed 64 cuts70064 = true := by
 decide +kernel
def cuts70065 : List PrefixCut := [⟨41,112497639,112497701⟩,
⟨64,176221337,176221433⟩]
theorem checked70065 : checkPrefixCuts (2^48) 9187491841 10 Manual.Count131072.C070065.packed 64 cuts70065 = true := by
 decide +kernel
def pointBounds70065 : List (Nat × Nat × Nat) := [(9187575808,115825210898788,115825600410745)]
theorem point_links_checked70065 : (cuts70065.take 1).map (fun c => (9187491841-1+2*2^10*c.k,115825098401149+c.lower,115825487913044+c.upper)) = pointBounds70065 := by
 decide +kernel
def cuts70066 : List PrefixCut := [⟨64,176647706,176647812⟩]
theorem checked70066 : checkPrefixCuts (2^48) 9187622913 10 Manual.Count131072.C070066.packed 64 cuts70066 = true := by
 decide +kernel
def cuts70067 : List PrefixCut := [⟨54,144294098,144294185⟩,
⟨64,171866024,171866127⟩]
theorem checked70067 : checkPrefixCuts (2^48) 9187753985 10 Manual.Count131072.C070067.packed 64 cuts70067 = true := by
 decide +kernel
def pointBounds70067 : List (Nat × Nat × Nat) := [(9187864576,115825595564290,115825985076474)]
theorem point_links_checked70067 : (cuts70067.take 1).map (fun c => (9187753985-1+2*2^10*c.k,115825451270192+c.lower,115825840782289+c.upper)) = pointBounds70067 := by
 decide +kernel
def cuts70068 : List PrefixCut := [⟨64,175509181,175509282⟩]
theorem checked70068 : checkPrefixCuts (2^48) 9187885057 10 Manual.Count131072.C070068.packed 64 cuts70068 = true := by
 decide +kernel
def cuts70069 : List PrefixCut := [⟨64,174985878,174985979⟩]
theorem checked70069 : checkPrefixCuts (2^48) 9188016129 10 Manual.Count131072.C070069.packed 64 cuts70069 = true := by
 decide +kernel
def cuts70070 : List PrefixCut := [⟨3,8332599,8332604⟩,
⟨64,175351007,175351114⟩]
theorem checked70070 : checkPrefixCuts (2^48) 9188147201 10 Manual.Count131072.C070070.packed 64 cuts70070 = true := by
 decide +kernel
def pointBounds70070 : List (Nat × Nat × Nat) := [(9188153344,115825981963874,115826371476281)]
theorem point_links_checked70070 : (cuts70070.take 1).map (fun c => (9188147201-1+2*2^10*c.k,115825973631275+c.lower,115826363143677+c.upper)) = pointBounds70070 := by
 decide +kernel
def cuts70071 : List PrefixCut := [⟨64,176451324,176451426⟩]
theorem checked70071 : checkPrefixCuts (2^48) 9188278273 10 Manual.Count131072.C070071.packed 64 cuts70071 = true := by
 decide +kernel
def cuts70072 : List PrefixCut := [⟨16,44173703,44173725⟩,
⟨64,175713609,175713702⟩]
theorem checked70072 : checkPrefixCuts (2^48) 9188409345 10 Manual.Count131072.C070072.packed 64 cuts70072 = true := by
 decide +kernel
def pointBounds70072 : List (Nat × Nat × Nat) := [(9188442112,115826369607309,115826759119942)]
theorem point_links_checked70072 : (cuts70072.take 1).map (fun c => (9188409345-1+2*2^10*c.k,115826325433606+c.lower,115826714946217+c.upper)) = pointBounds70072 := by
 decide +kernel
def cuts70073 : List PrefixCut := [⟨64,172892849,172892953⟩]
theorem checked70073 : checkPrefixCuts (2^48) 9188540417 10 Manual.Count131072.C070073.packed 64 cuts70073 = true := by
 decide +kernel
def cuts70074 : List PrefixCut := [⟨29,78879248,78879293⟩,
⟨64,173625569,173625672⟩]
theorem checked70074 : checkPrefixCuts (2^48) 9188671489 10 Manual.Count131072.C070074.packed 64 cuts70074 = true := by
 decide +kernel
def pointBounds70074 : List (Nat × Nat × Nat) := [(9188730880,115826752919312,115827142432165)]
theorem point_links_checked70074 : (cuts70074.take 1).map (fun c => (9188671489-1+2*2^10*c.k,115826674040064+c.lower,115827063552872+c.upper)) = pointBounds70074 := by
 decide +kernel
def cuts70075 : List PrefixCut := [⟨64,173224882,173224978⟩]
theorem checked70075 : checkPrefixCuts (2^48) 9188802561 10 Manual.Count131072.C070075.packed 64 cuts70075 = true := by
 decide +kernel
def cuts70076 : List PrefixCut := [⟨42,115175572,115175643⟩,
⟨64,174631475,174631575⟩]
theorem checked70076 : checkPrefixCuts (2^48) 9188933633 10 Manual.Count131072.C070076.packed 64 cuts70076 = true := by
 decide +kernel
def pointBounds70076 : List (Nat × Nat × Nat) := [(9189019648,115827136066087,115827525579165)]
theorem point_links_checked70076 : (cuts70076.take 1).map (fun c => (9188933633-1+2*2^10*c.k,115827020890515+c.lower,115827410403522+c.upper)) = pointBounds70076 := by
 decide +kernel
def cuts70077 : List PrefixCut := [⟨64,172515426,172515527⟩]
theorem checked70077 : checkPrefixCuts (2^48) 9189064705 10 Manual.Count131072.C070077.packed 64 cuts70077 = true := by
 decide +kernel
def cuts70078 : List PrefixCut := [⟨55,152603045,152603138⟩,
⟨64,176678745,176678853⟩]
theorem checked70078 : checkPrefixCuts (2^48) 9189195777 10 Manual.Count131072.C070078.packed 64 cuts70078 = true := by
 decide +kernel
def pointBounds70078 : List (Nat × Nat × Nat) := [(9189308416,115827520640461,115827910153762)]
theorem point_links_checked70078 : (cuts70078.take 1).map (fun c => (9189195777-1+2*2^10*c.k,115827368037416+c.lower,115827757550624+c.upper)) = pointBounds70078 := by
 decide +kernel
def cuts70079 : List PrefixCut := [⟨64,171591580,171591683⟩]
theorem checked70079 : checkPrefixCuts (2^48) 9189326849 10 Manual.Count131072.C070079.packed 64 cuts70079 = true := by
 decide +kernel
def cuts70080 : List PrefixCut := [⟨64,171926060,171926154⟩]
theorem checked70080 : checkPrefixCuts (2^48) 9189457921 10 Manual.Count131072.C070080.packed 64 cuts70080 = true := by
 decide +kernel
def cuts70081 : List PrefixCut := [⟨4,10628522,10628528⟩,
⟨64,176854968,176855077⟩]
theorem checked70081 : checkPrefixCuts (2^48) 9189588993 10 Manual.Count131072.C070081.packed 64 cuts70081 = true := by
 decide +kernel
def pointBounds70081 : List (Nat × Nat × Nat) := [(9189597184,115827898862323,115828288375842)]
theorem point_links_checked70081 : (cuts70081.take 1).map (fun c => (9189588993-1+2*2^10*c.k,115827888233801+c.lower,115828277747314+c.upper)) = pointBounds70081 := by
 decide +kernel
def cuts70082 : List PrefixCut := [⟨64,172840009,172840115⟩]
theorem checked70082 : checkPrefixCuts (2^48) 9189720065 10 Manual.Count131072.C070082.packed 64 cuts70082 = true := by
 decide +kernel
def cuts70083 : List PrefixCut := [⟨17,47903486,47903517⟩,
⟨64,175716663,175716768⟩]
theorem checked70083 : checkPrefixCuts (2^48) 9189851137 10 Manual.Count131072.C070083.packed 64 cuts70083 = true := by
 decide +kernel
def pointBounds70083 : List (Nat × Nat × Nat) := [(9189885952,115828285832264,115828675346023)]
theorem point_links_checked70083 : (cuts70083.take 1).map (fun c => (9189851137-1+2*2^10*c.k,115828237928778+c.lower,115828627442506+c.upper)) = pointBounds70083 := by
 decide +kernel
def cuts70084 : List PrefixCut := [⟨64,176051071,176051175⟩]
theorem checked70084 : checkPrefixCuts (2^48) 9189982209 10 Manual.Count131072.C070084.packed 64 cuts70084 = true := by
 decide +kernel
def cuts70085 : List PrefixCut := [⟨30,82603468,82603518⟩,
⟨64,173720848,173720953⟩]
theorem checked70085 : checkPrefixCuts (2^48) 9190113281 10 Manual.Count131072.C070085.packed 64 cuts70085 = true := by
 decide +kernel
def pointBounds70085 : List (Nat × Nat × Nat) := [(9190174720,115828672299980,115829061813967)]
theorem point_links_checked70085 : (cuts70085.take 1).map (fun c => (9190113281-1+2*2^10*c.k,115828589696512+c.lower,115828979210449+c.upper)) = pointBounds70085 := by
 decide +kernel
def cuts70086 : List PrefixCut := [⟨64,176872978,176873078⟩]
theorem checked70086 : checkPrefixCuts (2^48) 9190244353 10 Manual.Count131072.C070086.packed 64 cuts70086 = true := by
 decide +kernel
def cuts70087 : List PrefixCut := [⟨43,117209493,117209560⟩,
⟨64,175737256,175737358⟩]
theorem checked70087 : checkPrefixCuts (2^48) 9190375425 10 Manual.Count131072.C070087.packed 64 cuts70087 = true := by
 decide +kernel
def pointBounds70087 : List (Nat × Nat × Nat) := [(9190463488,115829057499831,115829447014040)]
theorem point_links_checked70087 : (cuts70087.take 1).map (fun c => (9190375425-1+2*2^10*c.k,115828940290338+c.lower,115829329804480+c.upper)) = pointBounds70087 := by
 decide +kernel
def cuts70088 : List PrefixCut := [⟨64,174846599,174846707⟩]
theorem checked70088 : checkPrefixCuts (2^48) 9190506497 10 Manual.Count131072.C070088.packed 64 cuts70088 = true := by
 decide +kernel
def cuts70089 : List PrefixCut := [⟨56,153375366,153375457⟩,
⟨64,175425980,175426085⟩]
theorem checked70089 : checkPrefixCuts (2^48) 9190637569 10 Manual.Count131072.C070089.packed 64 cuts70089 = true := by
 decide +kernel
def pointBounds70089 : List (Nat × Nat × Nat) := [(9190752256,115829444249559,115829833764002)]
theorem point_links_checked70089 : (cuts70089.take 1).map (fun c => (9190637569-1+2*2^10*c.k,115829290874193+c.lower,115829680388545+c.upper)) = pointBounds70089 := by
 decide +kernel
def cuts70090 : List PrefixCut := [⟨64,176372894,176372998⟩]
theorem checked70090 : checkPrefixCuts (2^48) 9190768641 10 Manual.Count131072.C070090.packed 64 cuts70090 = true := by
 decide +kernel
def cuts70091 : List PrefixCut := [⟨64,174471609,174471715⟩]
theorem checked70091 : checkPrefixCuts (2^48) 9190899713 10 Manual.Count131072.C070091.packed 64 cuts70091 = true := by
 decide +kernel
def cuts70092 : List PrefixCut := [⟨5,14087472,14087479⟩,
⟨64,175602233,175602335⟩]
theorem checked70092 : checkPrefixCuts (2^48) 9191030785 10 Manual.Count131072.C070092.packed 64 cuts70092 = true := by
 decide +kernel
def pointBounds70092 : List (Nat × Nat × Nat) := [(9191041024,115829831232148,115830220746822)]
theorem point_links_checked70092 : (cuts70092.take 1).map (fun c => (9191030785-1+2*2^10*c.k,115829817144676+c.lower,115830206659343+c.upper)) = pointBounds70092 := by
 decide +kernel
def cuts70093 : List PrefixCut := [⟨64,175599730,175599832⟩]
theorem checked70093 : checkPrefixCuts (2^48) 9191161857 10 Manual.Count131072.C070093.packed 64 cuts70093 = true := by
 decide +kernel
def cuts70094 : List PrefixCut := [⟨18,47773469,47773499⟩,
⟨64,174678501,174678603⟩]
theorem checked70094 : checkPrefixCuts (2^48) 9191292929 10 Manual.Count131072.C070094.packed 64 cuts70094 = true := by
 decide +kernel
def pointBounds70094 : List (Nat × Nat × Nat) := [(9191329792,115830216120108,115830605635009)]
theorem point_links_checked70094 : (cuts70094.take 1).map (fun c => (9191292929-1+2*2^10*c.k,115830168346639+c.lower,115830557861510+c.upper)) = pointBounds70094 := by
 decide +kernel
def cuts70095 : List PrefixCut := [⟨64,177677130,177677234⟩]
theorem checked70095 : checkPrefixCuts (2^48) 9191424001 10 Manual.Count131072.C070095.packed 64 cuts70095 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000002
