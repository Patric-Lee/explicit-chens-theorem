import PlattAssemblyKernel
import PlattCertificates.Count131072.C064064
import PlattCertificates.Count131072.C064065
import PlattCertificates.Count131072.C064066
import PlattCertificates.Count131072.C064067
import PlattCertificates.Count131072.C064068
import PlattCertificates.Count131072.C064069
import PlattCertificates.Count131072.C064070
import PlattCertificates.Count131072.C064071
import PlattCertificates.Count131072.C064072
import PlattCertificates.Count131072.C064073
import PlattCertificates.Count131072.C064074
import PlattCertificates.Count131072.C064075
import PlattCertificates.Count131072.C064076
import PlattCertificates.Count131072.C064077
import PlattCertificates.Count131072.C064078
import PlattCertificates.Count131072.C064079
import PlattCertificates.Count131072.C064080
import PlattCertificates.Count131072.C064081
import PlattCertificates.Count131072.C064082
import PlattCertificates.Count131072.C064083
import PlattCertificates.Count131072.C064084
import PlattCertificates.Count131072.C064085
import PlattCertificates.Count131072.C064086
import PlattCertificates.Count131072.C064087
import PlattCertificates.Count131072.C064088
import PlattCertificates.Count131072.C064089
import PlattCertificates.Count131072.C064090
import PlattCertificates.Count131072.C064091
import PlattCertificates.Count131072.C064092
import PlattCertificates.Count131072.C064093
import PlattCertificates.Count131072.C064094
import PlattCertificates.Count131072.C064095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000127
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64064 : List PrefixCut := [⟨64,190576151,190576262⟩]
theorem checked64064 : checkPrefixCuts (2^48) 8400928769 10 Manual.Count131072.C064064.packed 64 cuts64064 = true := by
 decide +kernel
def cuts64065 : List PrefixCut := [⟨31,94214831,94214881⟩,
⟨64,193253541,193253651⟩]
theorem checked64065 : checkPrefixCuts (2^48) 8401059841 10 Manual.Count131072.C064065.packed 64 cuts64065 = true := by
 decide +kernel
def pointBounds64065 : List (Nat × Nat × Nat) := [(8401123328,114725181207595,114725570078714)]
theorem point_links_checked64065 : (cuts64065.take 1).map (fun c => (8401059841-1+2*2^10*c.k,114725086992764+c.lower,114725475863833+c.upper)) = pointBounds64065 := by
 decide +kernel
def cuts64066 : List PrefixCut := [⟨64,192747961,192748071⟩]
theorem checked64066 : checkPrefixCuts (2^48) 8401190913 10 Manual.Count131072.C064066.packed 64 cuts64066 = true := by
 decide +kernel
def cuts64067 : List PrefixCut := [⟨32,98399818,98399875⟩,
⟨64,194788668,194788779⟩]
theorem checked64067 : checkPrefixCuts (2^48) 8401321985 10 Manual.Count131072.C064067.packed 64 cuts64067 = true := by
 decide +kernel
def pointBounds64067 : List (Nat × Nat × Nat) := [(8401387520,114725571394084,114725960265430)]
theorem point_links_checked64067 : (cuts64067.take 1).map (fun c => (8401321985-1+2*2^10*c.k,114725472994266+c.lower,114725861865555+c.upper)) = pointBounds64067 := by
 decide +kernel
def cuts64068 : List PrefixCut := [⟨64,192942961,192943068⟩]
theorem checked64068 : checkPrefixCuts (2^48) 8401453057 10 Manual.Count131072.C064068.packed 64 cuts64068 = true := by
 decide +kernel
def cuts64069 : List PrefixCut := [⟨33,101445463,101445518⟩,
⟨64,195318632,195318739⟩]
theorem checked64069 : checkPrefixCuts (2^48) 8401584129 10 Manual.Count131072.C064069.packed 64 cuts64069 = true := by
 decide +kernel
def pointBounds64069 : List (Nat × Nat × Nat) := [(8401651712,114725962171358,114726351042920)]
theorem point_links_checked64069 : (cuts64069.take 1).map (fun c => (8401584129-1+2*2^10*c.k,114725860725895+c.lower,114726249597402+c.upper)) = pointBounds64069 := by
 decide +kernel
def cuts64070 : List PrefixCut := [⟨64,191663877,191663994⟩]
theorem checked64070 : checkPrefixCuts (2^48) 8401715201 10 Manual.Count131072.C064070.packed 64 cuts64070 = true := by
 decide +kernel
def cuts64071 : List PrefixCut := [⟨34,100336733,100336792⟩,
⟨64,193804951,193805061⟩]
theorem checked64071 : checkPrefixCuts (2^48) 8401846273 10 Manual.Count131072.C064071.packed 64 cuts64071 = true := by
 decide +kernel
def pointBounds64071 : List (Nat × Nat × Nat) := [(8401915904,114726348045137,114726736916927)]
theorem point_links_checked64071 : (cuts64071.take 1).map (fun c => (8401846273-1+2*2^10*c.k,114726247708404+c.lower,114726636580135+c.upper)) = pointBounds64071 := by
 decide +kernel
def cuts64072 : List PrefixCut := [⟨64,193533940,193534049⟩]
theorem checked64072 : checkPrefixCuts (2^48) 8401977345 10 Manual.Count131072.C064072.packed 64 cuts64072 = true := by
 decide +kernel
def cuts64073 : List PrefixCut := [⟨35,102913116,102913176⟩,
⟨64,191085385,191085495⟩]
theorem checked64073 : checkPrefixCuts (2^48) 8402108417 10 Manual.Count131072.C064073.packed 64 cuts64073 = true := by
 decide +kernel
def pointBounds64073 : List (Nat × Nat × Nat) := [(8402180096,114726737960411,114727126832421)]
theorem point_links_checked64073 : (cuts64073.take 1).map (fun c => (8402108417-1+2*2^10*c.k,114726635047295+c.lower,114727023919245+c.upper)) = pointBounds64073 := by
 decide +kernel
def cuts64074 : List PrefixCut := [⟨64,192522908,192523008⟩]
theorem checked64074 : checkPrefixCuts (2^48) 8402239489 10 Manual.Count131072.C064074.packed 64 cuts64074 = true := by
 decide +kernel
def cuts64075 : List PrefixCut := [⟨36,106058832,106058893⟩,
⟨64,191112930,191113039⟩]
theorem checked64075 : checkPrefixCuts (2^48) 8402370561 10 Manual.Count131072.C064075.packed 64 cuts64075 = true := by
 decide +kernel
def pointBounds64075 : List (Nat × Nat × Nat) := [(8402444288,114727124714420,114727513586641)]
theorem point_links_checked64075 : (cuts64075.take 1).map (fun c => (8402370561-1+2*2^10*c.k,114727018655588+c.lower,114727407527748+c.upper)) = pointBounds64075 := by
 decide +kernel
def cuts64076 : List PrefixCut := [⟨64,191277449,191277561⟩]
theorem checked64076 : checkPrefixCuts (2^48) 8402501633 10 Manual.Count131072.C064076.packed 64 cuts64076 = true := by
 decide +kernel
def cuts64077 : List PrefixCut := [⟨37,111917707,111917770⟩,
⟨64,194054813,194054925⟩]
theorem checked64077 : checkPrefixCuts (2^48) 8402632705 10 Manual.Count131072.C064077.packed 64 cuts64077 = true := by
 decide +kernel
def pointBounds64077 : List (Nat × Nat × Nat) := [(8402708480,114727512963674,114727901836118)]
theorem point_links_checked64077 : (cuts64077.take 1).map (fun c => (8402632705-1+2*2^10*c.k,114727401045967+c.lower,114727789918348+c.upper)) = pointBounds64077 := by
 decide +kernel
def cuts64078 : List PrefixCut := [⟨64,192711887,192712002⟩]
theorem checked64078 : checkPrefixCuts (2^48) 8402763777 10 Manual.Count131072.C064078.packed 64 cuts64078 = true := by
 decide +kernel
def cuts64079 : List PrefixCut := [⟨38,113354583,113354648⟩,
⟨64,192239915,192240027⟩]
theorem checked64079 : checkPrefixCuts (2^48) 8402894849 10 Manual.Count131072.C064079.packed 64 cuts64079 = true := by
 decide +kernel
def pointBounds64079 : List (Nat × Nat × Nat) := [(8402972672,114727901167250,114728290039923)]
theorem point_links_checked64079 : (cuts64079.take 1).map (fun c => (8402894849-1+2*2^10*c.k,114727787812667+c.lower,114728176685275+c.upper)) = pointBounds64079 := by
 decide +kernel
def cuts64080 : List PrefixCut := [⟨64,192002440,192002553⟩]
theorem checked64080 : checkPrefixCuts (2^48) 8403025921 10 Manual.Count131072.C064080.packed 64 cuts64080 = true := by
 decide +kernel
def cuts64081 : List PrefixCut := [⟨39,117169603,117169672⟩,
⟨64,191564015,191564127⟩]
theorem checked64081 : checkPrefixCuts (2^48) 8403156993 10 Manual.Count131072.C064081.packed 64 cuts64081 = true := by
 decide +kernel
def pointBounds64081 : List (Nat × Nat × Nat) := [(8403236864,114728289224625,114728678097527)]
theorem point_links_checked64081 : (cuts64081.take 1).map (fun c => (8403156993-1+2*2^10*c.k,114728172055022+c.lower,114728560927855+c.upper)) = pointBounds64081 := by
 decide +kernel
def cuts64082 : List PrefixCut := [⟨64,191460534,191460640⟩]
theorem checked64082 : checkPrefixCuts (2^48) 8403288065 10 Manual.Count131072.C064082.packed 64 cuts64082 = true := by
 decide +kernel
def cuts64083 : List PrefixCut := [⟨40,120347963,120348029⟩,
⟨64,192830838,192830947⟩]
theorem checked64083 : checkPrefixCuts (2^48) 8403419137 10 Manual.Count131072.C064083.packed 64 cuts64083 = true := by
 decide +kernel
def pointBounds64083 : List (Nat × Nat × Nat) := [(8403501056,114728675427534,114729064300651)]
theorem point_links_checked64083 : (cuts64083.take 1).map (fun c => (8403419137-1+2*2^10*c.k,114728555079571+c.lower,114728943952622+c.upper)) = pointBounds64083 := by
 decide +kernel
def cuts64084 : List PrefixCut := [⟨64,192492870,192492988⟩]
theorem checked64084 : checkPrefixCuts (2^48) 8403550209 10 Manual.Count131072.C064084.packed 64 cuts64084 = true := by
 decide +kernel
def cuts64085 : List PrefixCut := [⟨41,120779612,120779683⟩,
⟨64,188973007,188973117⟩]
theorem checked64085 : checkPrefixCuts (2^48) 8403681281 10 Manual.Count131072.C064085.packed 64 cuts64085 = true := by
 decide +kernel
def pointBounds64085 : List (Nat × Nat × Nat) := [(8403765248,114729061182891,114729450056240)]
theorem point_links_checked64085 : (cuts64085.take 1).map (fun c => (8403681281-1+2*2^10*c.k,114728940403279+c.lower,114729329276557+c.upper)) = pointBounds64085 := by
 decide +kernel
def cuts64086 : List PrefixCut := [⟨64,192922286,192922400⟩]
theorem checked64086 : checkPrefixCuts (2^48) 8403812353 10 Manual.Count131072.C064086.packed 64 cuts64086 = true := by
 decide +kernel
def cuts64087 : List PrefixCut := [⟨42,124995946,124996021⟩,
⟨64,190373810,190373926⟩]
theorem checked64087 : checkPrefixCuts (2^48) 8403943425 10 Manual.Count131072.C064087.packed 64 cuts64087 = true := by
 decide +kernel
def pointBounds64087 : List (Nat × Nat × Nat) := [(8404029440,114729447294518,114729836168095)]
theorem point_links_checked64087 : (cuts64087.take 1).map (fun c => (8403943425-1+2*2^10*c.k,114729322298572+c.lower,114729711172074+c.upper)) = pointBounds64087 := by
 decide +kernel
def cuts64088 : List PrefixCut := [⟨64,191241669,191241779⟩]
theorem checked64088 : checkPrefixCuts (2^48) 8404074497 10 Manual.Count131072.C064088.packed 64 cuts64088 = true := by
 decide +kernel
def cuts64089 : List PrefixCut := [⟨43,130250281,130250352⟩,
⟨64,194487386,194487493⟩]
theorem checked64089 : checkPrefixCuts (2^48) 8404205569 10 Manual.Count131072.C064089.packed 64 cuts64089 = true := by
 decide +kernel
def pointBounds64089 : List (Nat × Nat × Nat) := [(8404293632,114729834164332,114730223038131)]
theorem point_links_checked64089 : (cuts64089.take 1).map (fun c => (8404205569-1+2*2^10*c.k,114729703914051+c.lower,114730092787779+c.upper)) = pointBounds64089 := by
 decide +kernel
def cuts64090 : List PrefixCut := [⟨64,190733316,190733423⟩]
theorem checked64090 : checkPrefixCuts (2^48) 8404336641 10 Manual.Count131072.C064090.packed 64 cuts64090 = true := by
 decide +kernel
def cuts64091 : List PrefixCut := [⟨44,133226893,133226972⟩,
⟨64,193911976,193912088⟩]
theorem checked64091 : checkPrefixCuts (2^48) 8404467713 10 Manual.Count131072.C064091.packed 64 cuts64091 = true := by
 decide +kernel
def pointBounds64091 : List (Nat × Nat × Nat) := [(8404557824,114730222361646,114730611235667)]
theorem point_links_checked64091 : (cuts64091.take 1).map (fun c => (8404467713-1+2*2^10*c.k,114730089134753+c.lower,114730478008695+c.upper)) = pointBounds64091 := by
 decide +kernel
def cuts64092 : List PrefixCut := [⟨64,187478810,187478921⟩]
theorem checked64092 : checkPrefixCuts (2^48) 8404598785 10 Manual.Count131072.C064092.packed 64 cuts64092 = true := by
 decide +kernel
def cuts64093 : List PrefixCut := [⟨45,132586420,132586498⟩,
⟨64,191695590,191695701⟩]
theorem checked64093 : checkPrefixCuts (2^48) 8404729857 10 Manual.Count131072.C064093.packed 64 cuts64093 = true := by
 decide +kernel
def pointBounds64093 : List (Nat × Nat × Nat) := [(8404822016,114730603111959,114730991986202)]
theorem point_links_checked64093 : (cuts64093.take 1).map (fun c => (8404729857-1+2*2^10*c.k,114730470525539+c.lower,114730859399704+c.upper)) = pointBounds64093 := by
 decide +kernel
def cuts64094 : List PrefixCut := [⟨64,191793090,191793204⟩]
theorem checked64094 : checkPrefixCuts (2^48) 8404860929 10 Manual.Count131072.C064094.packed 64 cuts64094 = true := by
 decide +kernel
def cuts64095 : List PrefixCut := [⟨46,137270704,137270789⟩,
⟨64,193698937,193699052⟩]
theorem checked64095 : checkPrefixCuts (2^48) 8404992001 10 Manual.Count131072.C064095.packed 64 cuts64095 = true := by
 decide +kernel
def pointBounds64095 : List (Nat × Nat × Nat) := [(8405086208,114730991284923,114731380159398)]
theorem point_links_checked64095 : (cuts64095.take 1).map (fun c => (8404992001-1+2*2^10*c.k,114730854014219+c.lower,114731242888609+c.upper)) = pointBounds64095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000127
