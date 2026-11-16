import PlattAssemblyKernel
import PlattCertificates.Count131072.C060032
import PlattCertificates.Count131072.C060033
import PlattCertificates.Count131072.C060034
import PlattCertificates.Count131072.C060035
import PlattCertificates.Count131072.C060036
import PlattCertificates.Count131072.C060037
import PlattCertificates.Count131072.C060038
import PlattCertificates.Count131072.C060039
import PlattCertificates.Count131072.C060040
import PlattCertificates.Count131072.C060041
import PlattCertificates.Count131072.C060042
import PlattCertificates.Count131072.C060043
import PlattCertificates.Count131072.C060044
import PlattCertificates.Count131072.C060045
import PlattCertificates.Count131072.C060046
import PlattCertificates.Count131072.C060047
import PlattCertificates.Count131072.C060048
import PlattCertificates.Count131072.C060049
import PlattCertificates.Count131072.C060050
import PlattCertificates.Count131072.C060051
import PlattCertificates.Count131072.C060052
import PlattCertificates.Count131072.C060053
import PlattCertificates.Count131072.C060054
import PlattCertificates.Count131072.C060055
import PlattCertificates.Count131072.C060056
import PlattCertificates.Count131072.C060057
import PlattCertificates.Count131072.C060058
import PlattCertificates.Count131072.C060059
import PlattCertificates.Count131072.C060060
import PlattCertificates.Count131072.C060061
import PlattCertificates.Count131072.C060062
import PlattCertificates.Count131072.C060063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60032 : List PrefixCut := [⟨64,205264505,205264626⟩]
theorem checked60032 : checkPrefixCuts (2^48) 7872446465 10 Manual.Count131072.C060032.packed 64 cuts60032 = true := by
 decide +kernel
def pointBounds60032 : List (Nat × Nat × Nat) := [(7872577536,113923588278132,113923976689218)]
theorem point_links_checked60032 : (cuts60032.take 1).map (fun c => (7872446465-1+2*2^10*c.k,113923383013627+c.lower,113923771424592+c.upper)) = pointBounds60032 := by
 decide +kernel
def cuts60033 : List PrefixCut := [⟨64,205046572,205046685⟩]
theorem checked60033 : checkPrefixCuts (2^48) 7872577537 10 Manual.Count131072.C060033.packed 64 cuts60033 = true := by
 decide +kernel
def cuts60034 : List PrefixCut := [⟨57,180624057,180624158⟩,
⟨64,203291258,203291373⟩]
theorem checked60034 : checkPrefixCuts (2^48) 7872708609 10 Manual.Count131072.C060034.packed 64 cuts60034 = true := by
 decide +kernel
def pointBounds60034 : List (Nat × Nat × Nat) := [(7872825344,113923973948761,113924362360061)]
theorem point_links_checked60034 : (cuts60034.take 1).map (fun c => (7872708609-1+2*2^10*c.k,113923793324704+c.lower,113924181735903+c.upper)) = pointBounds60034 := by
 decide +kernel
def cuts60035 : List PrefixCut := [⟨64,206148079,206148198⟩]
theorem checked60035 : checkPrefixCuts (2^48) 7872839681 10 Manual.Count131072.C060035.packed 64 cuts60035 = true := by
 decide +kernel
def cuts60036 : List PrefixCut := [⟨50,158058819,158058911⟩,
⟨64,204071029,204071149⟩]
theorem checked60036 : checkPrefixCuts (2^48) 7872970753 10 Manual.Count131072.C060036.packed 64 cuts60036 = true := by
 decide +kernel
def pointBounds60036 : List (Nat × Nat × Nat) := [(7873073152,113924360822860,113924749234385)]
theorem point_links_checked60036 : (cuts60036.take 1).map (fun c => (7872970753-1+2*2^10*c.k,113924202764041+c.lower,113924591175474+c.upper)) = pointBounds60036 := by
 decide +kernel
def cuts60037 : List PrefixCut := [⟨64,201350531,201350649⟩]
theorem checked60037 : checkPrefixCuts (2^48) 7873101825 10 Manual.Count131072.C060037.packed 64 cuts60037 = true := by
 decide +kernel
def cuts60038 : List PrefixCut := [⟨43,139284598,139284680⟩,
⟨64,207675051,207675174⟩]
theorem checked60038 : checkPrefixCuts (2^48) 7873232897 10 Manual.Count131072.C060038.packed 64 cuts60038 = true := by
 decide +kernel
def pointBounds60038 : List (Nat × Nat × Nat) := [(7873320960,113924747470199,113925135881952)]
theorem point_links_checked60038 : (cuts60038.take 1).map (fun c => (7873232897-1+2*2^10*c.k,113924608185601+c.lower,113924996597272+c.upper)) = pointBounds60038 := by
 decide +kernel
def cuts60039 : List PrefixCut := [⟨64,203345845,203345963⟩]
theorem checked60039 : checkPrefixCuts (2^48) 7873363969 10 Manual.Count131072.C060039.packed 64 cuts60039 = true := by
 decide +kernel
def cuts60040 : List PrefixCut := [⟨36,119582113,119582177⟩,
⟨64,206202449,206202567⟩]
theorem checked60040 : checkPrefixCuts (2^48) 7873495041 10 Manual.Count131072.C060040.packed 64 cuts60040 = true := by
 decide +kernel
def pointBounds60040 : List (Nat × Nat × Nat) := [(7873568768,113925138788610,113925527200586)]
theorem point_links_checked60040 : (cuts60040.take 1).map (fun c => (7873495041-1+2*2^10*c.k,113925019206497+c.lower,113925407618409+c.upper)) = pointBounds60040 := by
 decide +kernel
def cuts60041 : List PrefixCut := [⟨64,209952601,209952723⟩]
theorem checked60041 : checkPrefixCuts (2^48) 7873626113 10 Manual.Count131072.C060041.packed 64 cuts60041 = true := by
 decide +kernel
def cuts60042 : List PrefixCut := [⟨29,92981460,92981512⟩,
⟨64,205909562,205909680⟩]
theorem checked60042 : checkPrefixCuts (2^48) 7873757185 10 Manual.Count131072.C060042.packed 64 cuts60042 = true := by
 decide +kernel
def pointBounds60042 : List (Nat × Nat × Nat) := [(7873816576,113925528343007,113925916755211)]
theorem point_links_checked60042 : (cuts60042.take 1).map (fun c => (7873757185-1+2*2^10*c.k,113925435361547+c.lower,113925823773699+c.upper)) = pointBounds60042 := by
 decide +kernel
def cuts60043 : List PrefixCut := [⟨64,205048186,205048301⟩]
theorem checked60043 : checkPrefixCuts (2^48) 7873888257 10 Manual.Count131072.C060043.packed 64 cuts60043 = true := by
 decide +kernel
def cuts60044 : List PrefixCut := [⟨22,70636454,70636494⟩,
⟨64,206975112,206975231⟩]
theorem checked60044 : checkPrefixCuts (2^48) 7874019329 10 Manual.Count131072.C060044.packed 64 cuts60044 = true := by
 decide +kernel
def pointBounds60044 : List (Nat × Nat × Nat) := [(7874064384,113925916955749,113926305368174)]
theorem point_links_checked60044 : (cuts60044.take 1).map (fun c => (7874019329-1+2*2^10*c.k,113925846319295+c.lower,113926234731680+c.upper)) = pointBounds60044 := by
 decide +kernel
def cuts60045 : List PrefixCut := [⟨64,206757190,206757307⟩]
theorem checked60045 : checkPrefixCuts (2^48) 7874150401 10 Manual.Count131072.C060045.packed 64 cuts60045 = true := by
 decide +kernel
def cuts60046 : List PrefixCut := [⟨15,48149909,48149938⟩,
⟨64,206539273,206539394⟩]
theorem checked60046 : checkPrefixCuts (2^48) 7874281473 10 Manual.Count131072.C060046.packed 64 cuts60046 = true := by
 decide +kernel
def pointBounds60046 : List (Nat × Nat × Nat) := [(7874312192,113926308201506,113926696614156)]
theorem point_links_checked60046 : (cuts60046.take 1).map (fun c => (7874281473-1+2*2^10*c.k,113926260051597+c.lower,113926648464218+c.upper)) = pointBounds60046 := by
 decide +kernel
def cuts60047 : List PrefixCut := [⟨64,202818347,202818463⟩]
theorem checked60047 : checkPrefixCuts (2^48) 7874412545 10 Manual.Count131072.C060047.packed 64 cuts60047 = true := by
 decide +kernel
def cuts60048 : List PrefixCut := [⟨8,24699710,24699725⟩,
⟨64,207068582,207068702⟩]
theorem checked60048 : checkPrefixCuts (2^48) 7874543617 10 Manual.Count131072.C060048.packed 64 cuts60048 = true := by
 decide +kernel
def pointBounds60048 : List (Nat × Nat × Nat) := [(7874560000,113926694108927,113927082521800)]
theorem point_links_checked60048 : (cuts60048.take 1).map (fun c => (7874543617-1+2*2^10*c.k,113926669409217+c.lower,113927057822075+c.upper)) = pointBounds60048 := by
 decide +kernel
def cuts60049 : List PrefixCut := [⟨64,205671116,205671232⟩]
theorem checked60049 : checkPrefixCuts (2^48) 7874674689 10 Manual.Count131072.C060049.packed 64 cuts60049 = true := by
 decide +kernel
def cuts60050 : List PrefixCut := [⟨1,3181191,3181193⟩,
⟨64,202843945,202844066⟩]
theorem checked60050 : checkPrefixCuts (2^48) 7874805761 10 Manual.Count131072.C060050.packed 64 cuts60050 = true := by
 decide +kernel
def pointBounds60050 : List (Nat × Nat × Nat) := [(7874807808,113927085330106,113927473743202)]
theorem point_links_checked60050 : (cuts60050.take 1).map (fun c => (7874805761-1+2*2^10*c.k,113927082148915+c.lower,113927470562009+c.upper)) = pointBounds60050 := by
 decide +kernel
def cuts60051 : List PrefixCut := [⟨58,187113858,187113969⟩,
⟨64,207093951,207094073⟩]
theorem checked60051 : checkPrefixCuts (2^48) 7874936833 10 Manual.Count131072.C060051.packed 64 cuts60051 = true := by
 decide +kernel
def pointBounds60051 : List (Nat × Nat × Nat) := [(7875055616,113927472106718,113927860520044)]
theorem point_links_checked60051 : (cuts60051.take 1).map (fun c => (7874936833-1+2*2^10*c.k,113927284992860+c.lower,113927673406075+c.upper)) = pointBounds60051 := by
 decide +kernel
def cuts60052 : List PrefixCut := [⟨64,203123144,203123262⟩]
theorem checked60052 : checkPrefixCuts (2^48) 7875067905 10 Manual.Count131072.C060052.packed 64 cuts60052 = true := by
 decide +kernel
def cuts60053 : List PrefixCut := [⟨51,163232359,163232450⟩,
⟨64,205478701,205478817⟩]
theorem checked60053 : checkPrefixCuts (2^48) 7875198977 10 Manual.Count131072.C060053.packed 64 cuts60053 = true := by
 decide +kernel
def pointBounds60053 : List (Nat × Nat × Nat) := [(7875303424,113927858442314,113928246855860)]
theorem point_links_checked60053 : (cuts60053.take 1).map (fun c => (7875198977-1+2*2^10*c.k,113927695209955+c.lower,113928083623410+c.upper)) = pointBounds60053 := by
 decide +kernel
def cuts60054 : List PrefixCut := [⟨64,206761985,206762101⟩]
theorem checked60054 : checkPrefixCuts (2^48) 7875330049 10 Manual.Count131072.C060054.packed 64 cuts60054 = true := by
 decide +kernel
def cuts60055 : List PrefixCut := [⟨44,139316656,139316735⟩,
⟨64,204113729,204113846⟩]
theorem checked60055 : checkPrefixCuts (2^48) 7875461121 10 Manual.Count131072.C060055.packed 64 cuts60055 = true := by
 decide +kernel
def pointBounds60055 : List (Nat × Nat × Nat) := [(7875551232,113928246767297,113928635181063)]
theorem point_links_checked60055 : (cuts60055.take 1).map (fun c => (7875461121-1+2*2^10*c.k,113928107450641+c.lower,113928495864328+c.upper)) = pointBounds60055 := by
 decide +kernel
def cuts60056 : List PrefixCut := [⟨64,203788677,203788796⟩]
theorem checked60056 : checkPrefixCuts (2^48) 7875592193 10 Manual.Count131072.C060056.packed 64 cuts60056 = true := by
 decide +kernel
def cuts60057 : List PrefixCut := [⟨37,120656178,120656244⟩,
⟨64,206930347,206930463⟩]
theorem checked60057 : checkPrefixCuts (2^48) 7875723265 10 Manual.Count131072.C060057.packed 64 cuts60057 = true := by
 decide +kernel
def pointBounds60057 : List (Nat × Nat × Nat) := [(7875799040,113928636009225,113929024423214)]
theorem point_links_checked60057 : (cuts60057.take 1).map (fun c => (7875723265-1+2*2^10*c.k,113928515353047+c.lower,113928903766970+c.upper)) = pointBounds60057 := by
 decide +kernel
def cuts60058 : List PrefixCut := [⟨64,206390812,206390932⟩]
theorem checked60058 : checkPrefixCuts (2^48) 7875854337 10 Manual.Count131072.C060058.packed 64 cuts60058 = true := by
 decide +kernel
def cuts60059 : List PrefixCut := [⟨30,96350279,96350336⟩,
⟨64,205851309,205851431⟩]
theorem checked60059 : checkPrefixCuts (2^48) 7875985409 10 Manual.Count131072.C060059.packed 64 cuts60059 = true := by
 decide +kernel
def pointBounds60059 : List (Nat × Nat × Nat) := [(7876046848,113929025024485,113929413438701)]
theorem point_links_checked60059 : (cuts60059.take 1).map (fun c => (7875985409-1+2*2^10*c.k,113928928674206+c.lower,113929317088365+c.upper)) = pointBounds60059 := by
 decide +kernel
def cuts60060 : List PrefixCut := [⟨64,206062308,206062429⟩]
theorem checked60060 : checkPrefixCuts (2^48) 7876116481 10 Manual.Count131072.C060060.packed 64 cuts60060 = true := by
 decide +kernel
def cuts60061 : List PrefixCut := [⟨23,72403314,72403354⟩,
⟨64,205987396,205987511⟩]
theorem checked60061 : checkPrefixCuts (2^48) 7876247553 10 Manual.Count131072.C060061.packed 64 cuts60061 = true := by
 decide +kernel
def pointBounds60061 : List (Nat × Nat × Nat) := [(7876294656,113929412991137,113929801405579)]
theorem point_links_checked60061 : (cuts60061.take 1).map (fun c => (7876247553-1+2*2^10*c.k,113929340587823+c.lower,113929729002225+c.upper)) = pointBounds60061 := by
 decide +kernel
def cuts60062 : List PrefixCut := [⟨64,207306240,207306351⟩]
theorem checked60062 : checkPrefixCuts (2^48) 7876378625 10 Manual.Count131072.C060062.packed 64 cuts60062 = true := by
 decide +kernel
def cuts60063 : List PrefixCut := [⟨16,51817083,51817114⟩,
⟨64,203479062,203479179⟩]
theorem checked60063 : checkPrefixCuts (2^48) 7876509697 10 Manual.Count131072.C060063.packed 64 cuts60063 = true := by
 decide +kernel
def pointBounds60063 : List (Nat × Nat × Nat) := [(7876542464,113929805698542,113930194113201)]
theorem point_links_checked60063 : (cuts60063.take 1).map (fun c => (7876509697-1+2*2^10*c.k,113929753881459+c.lower,113930142296087+c.upper)) = pointBounds60063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000001
