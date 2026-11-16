import PlattAssemblyKernel
import PlattCertificates.Count131072.C036080
import PlattCertificates.Count131072.C036081
import PlattCertificates.Count131072.C036082
import PlattCertificates.Count131072.C036083
import PlattCertificates.Count131072.C036084
import PlattCertificates.Count131072.C036085
import PlattCertificates.Count131072.C036086
import PlattCertificates.Count131072.C036087
import PlattCertificates.Count131072.C036088
import PlattCertificates.Count131072.C036089
import PlattCertificates.Count131072.C036090
import PlattCertificates.Count131072.C036091
import PlattCertificates.Count131072.C036092
import PlattCertificates.Count131072.C036093
import PlattCertificates.Count131072.C036094
import PlattCertificates.Count131072.C036095
import PlattCertificates.Count131072.C036096
import PlattCertificates.Count131072.C036097
import PlattCertificates.Count131072.C036098
import PlattCertificates.Count131072.C036099
import PlattCertificates.Count131072.C036100
import PlattCertificates.Count131072.C036101
import PlattCertificates.Count131072.C036102
import PlattCertificates.Count131072.C036103
import PlattCertificates.Count131072.C036104
import PlattCertificates.Count131072.C036105
import PlattCertificates.Count131072.C036106
import PlattCertificates.Count131072.C036107
import PlattCertificates.Count131072.C036108
import PlattCertificates.Count131072.C036109
import PlattCertificates.Count131072.C036110
import PlattCertificates.Count131072.C036111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000190
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts36080 : List PrefixCut := [⟨8,42640340,42640365⟩,
⟨64,348314428,348314643⟩]
theorem checked36080 : checkPrefixCuts (2^48) 4733009921 10 Manual.Count131072.C036080.packed 64 cuts36080 = true := by
 decide +kernel
def pointBounds36080 : List (Nat × Nat × Nat) := [(4733026304,107567194489300,107567579209680)]
theorem point_links_checked36080 : (cuts36080.take 1).map (fun c => (4733009921-1+2*2^10*c.k,107567151848960+c.lower,107567536569315+c.upper)) = pointBounds36080 := by
 decide +kernel
def cuts36081 : List PrefixCut := [⟨17,94376858,94376918⟩,
⟨64,349375213,349375436⟩]
theorem checked36081 : checkPrefixCuts (2^48) 4733140993 10 Manual.Count131072.C036081.packed 64 cuts36081 = true := by
 decide +kernel
def pointBounds36081 : List (Nat × Nat × Nat) := [(4733175808,107567594540246,107567979260876)]
theorem point_links_checked36081 : (cuts36081.take 1).map (fun c => (4733140993-1+2*2^10*c.k,107567500163388+c.lower,107567884883958+c.upper)) = pointBounds36081 := by
 decide +kernel
def cuts36082 : List PrefixCut := [⟨26,142780185,142780273⟩,
⟨64,348057280,348057492⟩]
theorem checked36082 : checkPrefixCuts (2^48) 4733272065 10 Manual.Count131072.C036082.packed 64 cuts36082 = true := by
 decide +kernel
def pointBounds36082 : List (Nat × Nat × Nat) := [(4733325312,107567992318786,107568377039667)]
theorem point_links_checked36082 : (cuts36082.take 1).map (fun c => (4733272065-1+2*2^10*c.k,107567849538601+c.lower,107568234259394+c.upper)) = pointBounds36082 := by
 decide +kernel
def cuts36083 : List PrefixCut := [⟨35,194689063,194689183⟩,
⟨64,353280551,353280767⟩]
theorem checked36083 : checkPrefixCuts (2^48) 4733403137 10 Manual.Count131072.C036083.packed 64 cuts36083 = true := by
 decide +kernel
def pointBounds36083 : List (Nat × Nat × Nat) := [(4733474816,107568392284944,107568777006069)]
theorem point_links_checked36083 : (cuts36083.take 1).map (fun c => (4733403137-1+2*2^10*c.k,107568197595881+c.lower,107568582316886+c.upper)) = pointBounds36083 := by
 decide +kernel
def cuts36084 : List PrefixCut := [⟨44,247308413,247308561⟩,
⟨64,357373709,357373925⟩]
theorem checked36084 : checkPrefixCuts (2^48) 4733534209 10 Manual.Count131072.C036084.packed 64 cuts36084 = true := by
 decide +kernel
def pointBounds36084 : List (Nat × Nat × Nat) := [(4733624320,107568798184845,107569182906214)]
theorem point_links_checked36084 : (cuts36084.take 1).map (fun c => (4733534209-1+2*2^10*c.k,107568550876432+c.lower,107568935597653+c.upper)) = pointBounds36084 := by
 decide +kernel
def cuts36085 : List PrefixCut := [⟨53,283691678,283691853⟩,
⟨64,344876890,344877100⟩]
theorem checked36085 : checkPrefixCuts (2^48) 4733665281 10 Manual.Count131072.C036085.packed 64 cuts36085 = true := by
 decide +kernel
def pointBounds36085 : List (Nat × Nat × Nat) := [(4733773824,107569191941819,107569576663431)]
theorem point_links_checked36085 : (cuts36085.take 1).map (fun c => (4733665281-1+2*2^10*c.k,107568908250141+c.lower,107569292971578+c.upper)) = pointBounds36085 := by
 decide +kernel
def cuts36086 : List PrefixCut := [⟨62,337316092,337316297⟩,
⟨64,348434941,348435153⟩]
theorem checked36086 : checkPrefixCuts (2^48) 4733796353 10 Manual.Count131072.C036086.packed 64 cuts36086 = true := by
 decide +kernel
def pointBounds36086 : List (Nat × Nat × Nat) := [(4733923328,107569590443123,107569975164975)]
theorem point_links_checked36086 : (cuts36086.take 1).map (fun c => (4733796353-1+2*2^10*c.k,107569253127031+c.lower,107569637848678+c.upper)) = pointBounds36086 := by
 decide +kernel
def cuts36087 : List PrefixCut := [⟨64,352468438,352468655⟩]
theorem checked36087 : checkPrefixCuts (2^48) 4733927425 10 Manual.Count131072.C036087.packed 64 cuts36087 = true := by
 decide +kernel
def cuts36088 : List PrefixCut := [⟨7,38112149,38112171⟩,
⟨64,349842607,349842814⟩]
theorem checked36088 : checkPrefixCuts (2^48) 4734058497 10 Manual.Count131072.C036088.packed 64 cuts36088 = true := by
 decide +kernel
def pointBounds36088 : List (Nat × Nat × Nat) := [(4734072832,107569992142559,107570376864657)]
theorem point_links_checked36088 : (cuts36088.take 1).map (fun c => (4734058497-1+2*2^10*c.k,107569954030410+c.lower,107570338752486+c.upper)) = pointBounds36088 := by
 decide +kernel
def cuts36089 : List PrefixCut := [⟨16,85556555,85556609⟩,
⟨64,349119418,349119632⟩]
theorem checked36089 : checkPrefixCuts (2^48) 4734189569 10 Manual.Count131072.C036089.packed 64 cuts36089 = true := by
 decide +kernel
def pointBounds36089 : List (Nat × Nat × Nat) := [(4734222336,107570389429572,107570774151909)]
theorem point_links_checked36089 : (cuts36089.take 1).map (fun c => (4734189569-1+2*2^10*c.k,107570303873017+c.lower,107570688595300+c.upper)) = pointBounds36089 := by
 decide +kernel
def cuts36090 : List PrefixCut := [⟨25,136268122,136268204⟩,
⟨64,349169246,349169460⟩]
theorem checked36090 : checkPrefixCuts (2^48) 4734320641 10 Manual.Count131072.C036090.packed 64 cuts36090 = true := by
 decide +kernel
def pointBounds36090 : List (Nat × Nat × Nat) := [(4734371840,107570789260557,107571173983136)]
theorem point_links_checked36090 : (cuts36090.take 1).map (fun c => (4734320641-1+2*2^10*c.k,107570652992435+c.lower,107571037714932+c.upper)) = pointBounds36090 := by
 decide +kernel
def cuts36091 : List PrefixCut := [⟨34,183647373,183647483⟩,
⟨64,344344035,344344244⟩]
theorem checked36091 : checkPrefixCuts (2^48) 4734451713 10 Manual.Count131072.C036091.packed 64 cuts36091 = true := by
 decide +kernel
def pointBounds36091 : List (Nat × Nat × Nat) := [(4734521344,107571185809054,107571570531875)]
theorem point_links_checked36091 : (cuts36091.take 1).map (fun c => (4734451713-1+2*2^10*c.k,107571002161681+c.lower,107571386884392+c.upper)) = pointBounds36091 := by
 decide +kernel
def cuts36092 : List PrefixCut := [⟨43,234650283,234650431⟩,
⟨64,347604256,347604470⟩]
theorem checked36092 : checkPrefixCuts (2^48) 4734582785 10 Manual.Count131072.C036092.packed 64 cuts36092 = true := by
 decide +kernel
def pointBounds36092 : List (Nat × Nat × Nat) := [(4734670848,107571581155999,107571965879067)]
theorem point_links_checked36092 : (cuts36092.take 1).map (fun c => (4734582785-1+2*2^10*c.k,107571346505716+c.lower,107571731228636+c.upper)) = pointBounds36092 := by
 decide +kernel
def cuts36093 : List PrefixCut := [⟨52,284698990,284699163⟩,
⟨64,349259187,349259398⟩]
theorem checked36093 : checkPrefixCuts (2^48) 4734713857 10 Manual.Count131072.C036093.packed 64 cuts36093 = true := by
 decide +kernel
def pointBounds36093 : List (Nat × Nat × Nat) := [(4734820352,107571978808962,107572363532269)]
theorem point_links_checked36093 : (cuts36093.take 1).map (fun c => (4734713857-1+2*2^10*c.k,107571694109972+c.lower,107572078833106+c.upper)) = pointBounds36093 := by
 decide +kernel
def cuts36094 : List PrefixCut := [⟨61,331177870,331178080⟩,
⟨64,346098800,346099019⟩]
theorem checked36094 : checkPrefixCuts (2^48) 4734844929 10 Manual.Count131072.C036094.packed 64 cuts36094 = true := by
 decide +kernel
def pointBounds36094 : List (Nat × Nat × Nat) := [(4734969856,107572374547029,107572759270584)]
theorem point_links_checked36094 : (cuts36094.take 1).map (fun c => (4734844929-1+2*2^10*c.k,107572043369159+c.lower,107572428092504+c.upper)) = pointBounds36094 := by
 decide +kernel
def cuts36095 : List PrefixCut := [⟨64,353638750,353638966⟩]
theorem checked36095 : checkPrefixCuts (2^48) 4734976001 10 Manual.Count131072.C036095.packed 64 cuts36095 = true := by
 decide +kernel
def cuts36096 : List PrefixCut := [⟨6,33110403,33110424⟩,
⟨64,346198512,346198723⟩]
theorem checked36096 : checkPrefixCuts (2^48) 4735107073 10 Manual.Count131072.C036096.packed 64 cuts36096 = true := by
 decide +kernel
def pointBounds36096 : List (Nat × Nat × Nat) := [(4735119360,107572776217112,107573160940913)]
theorem point_links_checked36096 : (cuts36096.take 1).map (fun c => (4735107073-1+2*2^10*c.k,107572743106709+c.lower,107573127830489+c.upper)) = pointBounds36096 := by
 decide +kernel
def cuts36097 : List PrefixCut := [⟨15,82565512,82565560⟩,
⟨64,346902260,346902469⟩]
theorem checked36097 : checkPrefixCuts (2^48) 4735238145 10 Manual.Count131072.C036097.packed 64 cuts36097 = true := by
 decide +kernel
def pointBounds36097 : List (Nat × Nat × Nat) := [(4735268864,107573171870733,107573556594772)]
theorem point_links_checked36097 : (cuts36097.take 1).map (fun c => (4735238145-1+2*2^10*c.k,107573089305221+c.lower,107573474029212+c.upper)) = pointBounds36097 := by
 decide +kernel
def cuts36098 : List PrefixCut := [⟨24,128035162,128035245⟩,
⟨64,349626854,349627073⟩]
theorem checked36098 : checkPrefixCuts (2^48) 4735369217 10 Manual.Count131072.C036098.packed 64 cuts36098 = true := by
 decide +kernel
def pointBounds36098 : List (Nat × Nat × Nat) := [(4735418368,107573564242643,107573948966926)]
theorem point_links_checked36098 : (cuts36098.take 1).map (fun c => (4735369217-1+2*2^10*c.k,107573436207481+c.lower,107573820931681+c.upper)) = pointBounds36098 := by
 decide +kernel
def cuts36099 : List PrefixCut := [⟨33,175225845,175225949⟩,
⟨64,343911087,343911295⟩]
theorem checked36099 : checkPrefixCuts (2^48) 4735500289 10 Manual.Count131072.C036099.packed 64 cuts36099 = true := by
 decide +kernel
def pointBounds36099 : List (Nat × Nat × Nat) := [(4735567872,107573961060180,107574345784703)]
theorem point_links_checked36099 : (cuts36099.take 1).map (fun c => (4735500289-1+2*2^10*c.k,107573785834335+c.lower,107574170558754+c.upper)) = pointBounds36099 := by
 decide +kernel
def cuts36100 : List PrefixCut := [⟨42,231507634,231507777⟩,
⟨64,349191515,349191727⟩]
theorem checked36100 : checkPrefixCuts (2^48) 4735631361 10 Manual.Count131072.C036100.packed 64 cuts36100 = true := by
 decide +kernel
def pointBounds36100 : List (Nat × Nat × Nat) := [(4735717376,107574361253056,107574745977826)]
theorem point_links_checked36100 : (cuts36100.take 1).map (fun c => (4735631361-1+2*2^10*c.k,107574129745422+c.lower,107574514470049+c.upper)) = pointBounds36100 := by
 decide +kernel
def cuts36101 : List PrefixCut := [⟨51,282971788,282971960⟩,
⟨64,352331899,352332116⟩]
theorem checked36101 : checkPrefixCuts (2^48) 4735762433 10 Manual.Count131072.C036101.packed 64 cuts36101 = true := by
 decide +kernel
def pointBounds36101 : List (Nat × Nat × Nat) := [(4735866880,107574761908725,107575146633736)]
theorem point_links_checked36101 : (cuts36101.take 1).map (fun c => (4735762433-1+2*2^10*c.k,107574478936937+c.lower,107574863661776+c.upper)) = pointBounds36101 := by
 decide +kernel
def cuts36102 : List PrefixCut := [⟨60,330807495,330807694⟩,
⟨64,351846702,351846913⟩]
theorem checked36102 : checkPrefixCuts (2^48) 4735893505 10 Manual.Count131072.C036102.packed 64 cuts36102 = true := by
 decide +kernel
def pointBounds36102 : List (Nat × Nat × Nat) := [(4736016384,107575162076331,107575546801586)]
theorem point_links_checked36102 : (cuts36102.take 1).map (fun c => (4735893505-1+2*2^10*c.k,107574831268836+c.lower,107575215993892+c.upper)) = pointBounds36102 := by
 decide +kernel
def cuts36103 : List PrefixCut := [⟨64,348627612,348627829⟩]
theorem checked36103 : checkPrefixCuts (2^48) 4736024577 10 Manual.Count131072.C036103.packed 64 cuts36103 = true := by
 decide +kernel
def cuts36104 : List PrefixCut := [⟨5,26981686,26981702⟩,
⟨64,349449961,349450172⟩]
theorem checked36104 : checkPrefixCuts (2^48) 4736155649 10 Manual.Count131072.C036104.packed 64 cuts36104 = true := by
 decide +kernel
def pointBounds36104 : List (Nat × Nat × Nat) := [(4736165888,107575558724836,107575943450336)]
theorem point_links_checked36104 : (cuts36104.take 1).map (fun c => (4736155649-1+2*2^10*c.k,107575531743150+c.lower,107575916468634+c.upper)) = pointBounds36104 := by
 decide +kernel
def cuts36105 : List PrefixCut := [⟨14,77020326,77020373⟩,
⟨64,352055130,352055347⟩]
theorem checked36105 : checkPrefixCuts (2^48) 4736286721 10 Manual.Count131072.C036105.packed 64 cuts36105 = true := by
 decide +kernel
def pointBounds36105 : List (Nat × Nat × Nat) := [(4736315392,107575958213437,107576342939179)]
theorem point_links_checked36105 : (cuts36105.take 1).map (fun c => (4736286721-1+2*2^10*c.k,107575881193111+c.lower,107576265918806+c.upper)) = pointBounds36105 := by
 decide +kernel
def cuts36106 : List PrefixCut := [⟨23,125154321,125154402⟩,
⟨64,346459298,346459513⟩]
theorem checked36106 : checkPrefixCuts (2^48) 4736417793 10 Manual.Count131072.C036106.packed 64 cuts36106 = true := by
 decide +kernel
def pointBounds36106 : List (Nat × Nat × Nat) := [(4736464896,107576358402562,107576743128555)]
theorem point_links_checked36106 : (cuts36106.take 1).map (fun c => (4736417793-1+2*2^10*c.k,107576233248241+c.lower,107576617974153+c.upper)) = pointBounds36106 := by
 decide +kernel
def cuts36107 : List PrefixCut := [⟨32,178039536,178039649⟩,
⟨64,352154554,352154773⟩]
theorem checked36107 : checkPrefixCuts (2^48) 4736548865 10 Manual.Count131072.C036107.packed 64 cuts36107 = true := by
 decide +kernel
def pointBounds36107 : List (Nat × Nat × Nat) := [(4736614400,107576757747075,107577142473315)]
theorem point_links_checked36107 : (cuts36107.take 1).map (fun c => (4736548865-1+2*2^10*c.k,107576579707539+c.lower,107576964433666+c.upper)) = pointBounds36107 := by
 decide +kernel
def cuts36108 : List PrefixCut := [⟨41,221057209,221057346⟩,
⟨64,345727000,345727215⟩]
theorem checked36108 : checkPrefixCuts (2^48) 4736679937 10 Manual.Count131072.C036108.packed 64 cuts36108 = true := by
 decide +kernel
def pointBounds36108 : List (Nat × Nat × Nat) := [(4736763904,107577152919302,107577537645785)]
theorem point_links_checked36108 : (cuts36108.take 1).map (fun c => (4736679937-1+2*2^10*c.k,107576931862093+c.lower,107577316588439+c.upper)) = pointBounds36108 := by
 decide +kernel
def cuts36109 : List PrefixCut := [⟨50,274114703,274114872⟩,
⟨64,349936411,349936627⟩]
theorem checked36109 : checkPrefixCuts (2^48) 4736811009 10 Manual.Count131072.C036109.packed 64 cuts36109 = true := by
 decide +kernel
def pointBounds36109 : List (Nat × Nat × Nat) := [(4736913408,107577551703796,107577936430526)]
theorem point_links_checked36109 : (cuts36109.take 1).map (fun c => (4736811009-1+2*2^10*c.k,107577277589093+c.lower,107577662315654+c.upper)) = pointBounds36109 := by
 decide +kernel
def cuts36110 : List PrefixCut := [⟨59,322474877,322475076⟩,
⟨64,350283270,350283487⟩]
theorem checked36110 : checkPrefixCuts (2^48) 4736942081 10 Manual.Count131072.C036110.packed 64 cuts36110 = true := by
 decide +kernel
def pointBounds36110 : List (Nat × Nat × Nat) := [(4737062912,107577950000381,107578334727357)]
theorem point_links_checked36110 : (cuts36110.take 1).map (fun c => (4736942081-1+2*2^10*c.k,107577627525504+c.lower,107578012252281+c.upper)) = pointBounds36110 := by
 decide +kernel
def cuts36111 : List PrefixCut := [⟨64,353541611,353541823⟩]
theorem checked36111 : checkPrefixCuts (2^48) 4737073153 10 Manual.Count131072.C036111.packed 64 cuts36111 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000190
