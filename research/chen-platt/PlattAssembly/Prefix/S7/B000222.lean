import PlattAssemblyKernel
import PlattCertificates.Count131072.C067104
import PlattCertificates.Count131072.C067105
import PlattCertificates.Count131072.C067106
import PlattCertificates.Count131072.C067107
import PlattCertificates.Count131072.C067108
import PlattCertificates.Count131072.C067109
import PlattCertificates.Count131072.C067110
import PlattCertificates.Count131072.C067111
import PlattCertificates.Count131072.C067112
import PlattCertificates.Count131072.C067113
import PlattCertificates.Count131072.C067114
import PlattCertificates.Count131072.C067115
import PlattCertificates.Count131072.C067116
import PlattCertificates.Count131072.C067117
import PlattCertificates.Count131072.C067118
import PlattCertificates.Count131072.C067119
import PlattCertificates.Count131072.C067120
import PlattCertificates.Count131072.C067121
import PlattCertificates.Count131072.C067122
import PlattCertificates.Count131072.C067123
import PlattCertificates.Count131072.C067124
import PlattCertificates.Count131072.C067125
import PlattCertificates.Count131072.C067126
import PlattCertificates.Count131072.C067127
import PlattCertificates.Count131072.C067128
import PlattCertificates.Count131072.C067129
import PlattCertificates.Count131072.C067130
import PlattCertificates.Count131072.C067131
import PlattCertificates.Count131072.C067132
import PlattCertificates.Count131072.C067133
import PlattCertificates.Count131072.C067134
import PlattCertificates.Count131072.C067135
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000222
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts67104 : List PrefixCut := [⟨64,185625043,185625150⟩]
theorem checked67104 : checkPrefixCuts (2^48) 8799387649 10 Manual.Count131072.C067104.packed 64 cuts67104 = true := by
 decide +kernel
def cuts67105 : List PrefixCut := [⟨3,9052469,9052474⟩,
⟨64,182615475,182615581⟩]
theorem checked67105 : checkPrefixCuts (2^48) 8799518721 10 Manual.Count131072.C067105.packed 64 cuts67105 = true := by
 decide +kernel
def pointBounds67105 : List (Nat × Nat × Nat) := [(8799524864,115295275729538,115295664931071)]
theorem point_links_checked67105 : (cuts67105.take 1).map (fun c => (8799518721-1+2*2^10*c.k,115295266677069+c.lower,115295655878597+c.upper)) = pointBounds67105 := by
 decide +kernel
def cuts67106 : List PrefixCut := [⟨64,182100948,182101053⟩]
theorem checked67106 : checkPrefixCuts (2^48) 8799649793 10 Manual.Count131072.C067106.packed 64 cuts67106 = true := by
 decide +kernel
def cuts67107 : List PrefixCut := [⟨10,29171727,29171744⟩,
⟨64,183441673,183441781⟩]
theorem checked67107 : checkPrefixCuts (2^48) 8799780865 10 Manual.Count131072.C067107.packed 64 cuts67107 = true := by
 decide +kernel
def pointBounds67107 : List (Nat × Nat × Nat) := [(8799801344,115295660565219,115296049766975)]
theorem point_links_checked67107 : (cuts67107.take 1).map (fun c => (8799780865-1+2*2^10*c.k,115295631393492+c.lower,115296020595231+c.upper)) = pointBounds67107 := by
 decide +kernel
def cuts67108 : List PrefixCut := [⟨64,184046659,184046769⟩]
theorem checked67108 : checkPrefixCuts (2^48) 8799911937 10 Manual.Count131072.C067108.packed 64 cuts67108 = true := by
 decide +kernel
def cuts67109 : List PrefixCut := [⟨17,48426144,48426172⟩,
⟨64,179533995,179534102⟩]
theorem checked67109 : checkPrefixCuts (2^48) 8800043009 10 Manual.Count131072.C067109.packed 64 cuts67109 = true := by
 decide +kernel
def pointBounds67109 : List (Nat × Nat × Nat) := [(8800077824,115296047307968,115296436509953)]
theorem point_links_checked67109 : (cuts67109.take 1).map (fun c => (8800043009-1+2*2^10*c.k,115295998881824+c.lower,115296388083781+c.upper)) = pointBounds67109 := by
 decide +kernel
def cuts67110 : List PrefixCut := [⟨64,184393035,184393139⟩]
theorem checked67110 : checkPrefixCuts (2^48) 8800174081 10 Manual.Count131072.C067110.packed 64 cuts67110 = true := by
 decide +kernel
def cuts67111 : List PrefixCut := [⟨24,69214647,69214684⟩,
⟨64,182950976,182951084⟩]
theorem checked67111 : checkPrefixCuts (2^48) 8800305153 10 Manual.Count131072.C067111.packed 64 cuts67111 = true := by
 decide +kernel
def pointBounds67111 : List (Nat × Nat × Nat) := [(8800354304,115296432023501,115296821225706)]
theorem point_links_checked67111 : (cuts67111.take 1).map (fun c => (8800305153-1+2*2^10*c.k,115296362808854+c.lower,115296752011022+c.upper)) = pointBounds67111 := by
 decide +kernel
def cuts67112 : List PrefixCut := [⟨64,185123164,185123270⟩]
theorem checked67112 : checkPrefixCuts (2^48) 8800436225 10 Manual.Count131072.C067112.packed 64 cuts67112 = true := by
 decide +kernel
def cuts67113 : List PrefixCut := [⟨31,87699049,87699099⟩,
⟨64,183169399,183169507⟩]
theorem checked67113 : checkPrefixCuts (2^48) 8800567297 10 Manual.Count131072.C067113.packed 64 cuts67113 = true := by
 decide +kernel
def pointBounds67113 : List (Nat × Nat × Nat) := [(8800630784,115296818582043,115297207784475)]
theorem point_links_checked67113 : (cuts67113.take 1).map (fun c => (8800567297-1+2*2^10*c.k,115296730882994+c.lower,115297120085376+c.upper)) = pointBounds67113 := by
 decide +kernel
def cuts67114 : List PrefixCut := [⟨64,181951334,181951437⟩]
theorem checked67114 : checkPrefixCuts (2^48) 8800698369 10 Manual.Count131072.C067114.packed 64 cuts67114 = true := by
 decide +kernel
def cuts67115 : List PrefixCut := [⟨38,108804901,108804968⟩,
⟨64,183899552,183899663⟩]
theorem checked67115 : checkPrefixCuts (2^48) 8800829441 10 Manual.Count131072.C067115.packed 64 cuts67115 = true := by
 decide +kernel
def pointBounds67115 : List (Nat × Nat × Nat) := [(8800907264,115297204808628,115297594011288)]
theorem point_links_checked67115 : (cuts67115.take 1).map (fun c => (8800829441-1+2*2^10*c.k,115297096003727+c.lower,115297485206320+c.upper)) = pointBounds67115 := by
 decide +kernel
def cuts67116 : List PrefixCut := [⟨64,184280600,184280706⟩]
theorem checked67116 : checkPrefixCuts (2^48) 8800960513 10 Manual.Count131072.C067116.packed 64 cuts67116 = true := by
 decide +kernel
def cuts67117 : List PrefixCut := [⟨45,126839208,126839285⟩,
⟨64,181719307,181719418⟩]
theorem checked67117 : checkPrefixCuts (2^48) 8801091585 10 Manual.Count131072.C067117.packed 64 cuts67117 = true := by
 decide +kernel
def pointBounds67117 : List (Nat × Nat × Nat) := [(8801183744,115297591023087,115297980225974)]
theorem point_links_checked67117 : (cuts67117.take 1).map (fun c => (8801091585-1+2*2^10*c.k,115297464183879+c.lower,115297853386689+c.upper)) = pointBounds67117 := by
 decide +kernel
def cuts67118 : List PrefixCut := [⟨64,186098035,186098146⟩]
theorem checked67118 : checkPrefixCuts (2^48) 8801222657 10 Manual.Count131072.C067118.packed 64 cuts67118 = true := by
 decide +kernel
def cuts67119 : List PrefixCut := [⟨52,148901999,148902086⟩,
⟨64,183728691,183728796⟩]
theorem checked67119 : checkPrefixCuts (2^48) 8801353729 10 Manual.Count131072.C067119.packed 64 cuts67119 = true := by
 decide +kernel
def pointBounds67119 : List (Nat × Nat × Nat) := [(8801460224,115297980903220,115298370106339)]
theorem point_links_checked67119 : (cuts67119.take 1).map (fun c => (8801353729-1+2*2^10*c.k,115297832001221+c.lower,115298221204253+c.upper)) = pointBounds67119 := by
 decide +kernel
def cuts67120 : List PrefixCut := [⟨64,181999025,181999134⟩]
theorem checked67120 : checkPrefixCuts (2^48) 8801484801 10 Manual.Count131072.C067120.packed 64 cuts67120 = true := by
 decide +kernel
def cuts67121 : List PrefixCut := [⟨59,167861395,167861499⟩,
⟨64,182092251,182092364⟩]
theorem checked67121 : checkPrefixCuts (2^48) 8801615873 10 Manual.Count131072.C067121.packed 64 cuts67121 = true := by
 decide +kernel
def pointBounds67121 : List (Nat × Nat × Nat) := [(8801736704,115298365590332,115298754793682)]
theorem point_links_checked67121 : (cuts67121.take 1).map (fun c => (8801615873-1+2*2^10*c.k,115298197728937+c.lower,115298586932183+c.upper)) = pointBounds67121 := by
 decide +kernel
def cuts67122 : List PrefixCut := [⟨64,181769750,181769852⟩]
theorem checked67122 : checkPrefixCuts (2^48) 8801746945 10 Manual.Count131072.C067122.packed 64 cuts67122 = true := by
 decide +kernel
def cuts67123 : List PrefixCut := [⟨64,183653790,183653896⟩]
theorem checked67123 : checkPrefixCuts (2^48) 8801878017 10 Manual.Count131072.C067123.packed 64 cuts67123 = true := by
 decide +kernel
def cuts67124 : List PrefixCut := [⟨2,5596234,5596236⟩,
⟨64,180581131,180581238⟩]
theorem checked67124 : checkPrefixCuts (2^48) 8802009089 10 Manual.Count131072.C067124.packed 64 cuts67124 = true := by
 decide +kernel
def pointBounds67124 : List (Nat × Nat × Nat) := [(8802013184,115298750840962,115299140044531)]
theorem point_links_checked67124 : (cuts67124.take 1).map (fun c => (8802009089-1+2*2^10*c.k,115298745244728+c.lower,115299134448295+c.upper)) = pointBounds67124 := by
 decide +kernel
def cuts67125 : List PrefixCut := [⟨64,180642401,180642515⟩]
theorem checked67125 : checkPrefixCuts (2^48) 8802140161 10 Manual.Count131072.C067125.packed 64 cuts67125 = true := by
 decide +kernel
def cuts67126 : List PrefixCut := [⟨9,25741885,25741900⟩,
⟨64,182878149,182878253⟩]
theorem checked67126 : checkPrefixCuts (2^48) 8802271233 10 Manual.Count131072.C067126.packed 64 cuts67126 = true := by
 decide +kernel
def pointBounds67126 : List (Nat × Nat × Nat) := [(8802289664,115299132210145,115299521413948)]
theorem point_links_checked67126 : (cuts67126.take 1).map (fun c => (8802271233-1+2*2^10*c.k,115299106468260+c.lower,115299495672048+c.upper)) = pointBounds67126 := by
 decide +kernel
def cuts67127 : List PrefixCut := [⟨64,184186463,184186574⟩]
theorem checked67127 : checkPrefixCuts (2^48) 8802402305 10 Manual.Count131072.C067127.packed 64 cuts67127 = true := by
 decide +kernel
def cuts67128 : List PrefixCut := [⟨16,44063640,44063668⟩,
⟨64,180730265,180730371⟩]
theorem checked67128 : checkPrefixCuts (2^48) 8802533377 10 Manual.Count131072.C067128.packed 64 cuts67128 = true := by
 decide +kernel
def pointBounds67128 : List (Nat × Nat × Nat) := [(8802566144,115299517596512,115299906800543)]
theorem point_links_checked67128 : (cuts67128.take 1).map (fun c => (8802533377-1+2*2^10*c.k,115299473532872+c.lower,115299862736875+c.upper)) = pointBounds67128 := by
 decide +kernel
def cuts67129 : List PrefixCut := [⟨64,184948393,184948501⟩]
theorem checked67129 : checkPrefixCuts (2^48) 8802664449 10 Manual.Count131072.C067129.packed 64 cuts67129 = true := by
 decide +kernel
def cuts67130 : List PrefixCut := [⟨23,65613807,65613846⟩,
⟨64,183826501,183826609⟩]
theorem checked67130 : checkPrefixCuts (2^48) 8802795521 10 Manual.Count131072.C067130.packed 64 cuts67130 = true := by
 decide +kernel
def pointBounds67130 : List (Nat × Nat × Nat) := [(8802842624,115299904825337,115300294029593)]
theorem point_links_checked67130 : (cuts67130.take 1).map (fun c => (8802795521-1+2*2^10*c.k,115299839211530+c.lower,115300228415747+c.upper)) = pointBounds67130 := by
 decide +kernel
def cuts67131 : List PrefixCut := [⟨64,185006827,185006927⟩]
theorem checked67131 : checkPrefixCuts (2^48) 8802926593 10 Manual.Count131072.C067131.packed 64 cuts67131 = true := by
 decide +kernel
def cuts67132 : List PrefixCut := [⟨30,86459212,86459264⟩,
⟨64,184524465,184524578⟩]
theorem checked67132 : checkPrefixCuts (2^48) 8803057665 10 Manual.Count131072.C067132.packed 64 cuts67132 = true := by
 decide +kernel
def pointBounds67132 : List (Nat × Nat × Nat) := [(8803119104,115300294504070,115300683708547)]
theorem point_links_checked67132 : (cuts67132.take 1).map (fun c => (8803057665-1+2*2^10*c.k,115300208044858+c.lower,115300597249283+c.upper)) = pointBounds67132 := by
 decide +kernel
def cuts67133 : List PrefixCut := [⟨64,182986971,182987079⟩]
theorem checked67133 : checkPrefixCuts (2^48) 8803188737 10 Manual.Count131072.C067133.packed 64 cuts67133 = true := by
 decide +kernel
def cuts67134 : List PrefixCut := [⟨37,105352955,105353019⟩,
⟨64,183048185,183048293⟩]
theorem checked67134 : checkPrefixCuts (2^48) 8803319809 10 Manual.Count131072.C067134.packed 64 cuts67134 = true := by
 decide +kernel
def pointBounds67134 : List (Nat × Nat × Nat) := [(8803395584,115300680909249,115301070113959)]
theorem point_links_checked67134 : (cuts67134.take 1).map (fun c => (8803319809-1+2*2^10*c.k,115300575556294+c.lower,115300964760940+c.upper)) = pointBounds67134 := by
 decide +kernel
def cuts67135 : List PrefixCut := [⟨64,181798511,181798623⟩]
theorem checked67135 : checkPrefixCuts (2^48) 8803450881 10 Manual.Count131072.C067135.packed 64 cuts67135 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000222
