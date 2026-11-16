import PlattAssemblyKernel
import PlattCertificates.Count131072.C022080
import PlattCertificates.Count131072.C022081
import PlattCertificates.Count131072.C022082
import PlattCertificates.Count131072.C022083
import PlattCertificates.Count131072.C022084
import PlattCertificates.Count131072.C022085
import PlattCertificates.Count131072.C022086
import PlattCertificates.Count131072.C022087
import PlattCertificates.Count131072.C022088
import PlattCertificates.Count131072.C022089
import PlattCertificates.Count131072.C022090
import PlattCertificates.Count131072.C022091
import PlattCertificates.Count131072.C022092
import PlattCertificates.Count131072.C022093
import PlattCertificates.Count131072.C022094
import PlattCertificates.Count131072.C022095
import PlattCertificates.Count131072.C022096
import PlattCertificates.Count131072.C022097
import PlattCertificates.Count131072.C022098
import PlattCertificates.Count131072.C022099
import PlattCertificates.Count131072.C022100
import PlattCertificates.Count131072.C022101
import PlattCertificates.Count131072.C022102
import PlattCertificates.Count131072.C022103
import PlattCertificates.Count131072.C022104
import PlattCertificates.Count131072.C022105
import PlattCertificates.Count131072.C022106
import PlattCertificates.Count131072.C022107
import PlattCertificates.Count131072.C022108
import PlattCertificates.Count131072.C022109
import PlattCertificates.Count131072.C022110
import PlattCertificates.Count131072.C022111
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000065
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22080 : List PrefixCut := [⟨40,182695047,182695150⟩,
⟨128,590811493,590811818⟩]
theorem checked22080 : checkPrefixCuts (2^48) 2898001921 9 Manual.Count131072.C022080.packed 128 cuts22080 = true := by
 decide +kernel
def pointBounds22080 : List (Nat × Nat × Nat) := [(2898042880,101300284248379,101300665359566)]
theorem point_links_checked22080 : (cuts22080.take 1).map (fun c => (2898001921-1+2*2^9*c.k,101300101553332+c.lower,101300482664416+c.upper)) = pointBounds22080 := by
 decide +kernel
def cuts22081 : List PrefixCut := [⟨1,3982036,3982038⟩,
⟨90,411405734,411405974⟩,
⟨128,586511476,586511815⟩]
theorem checked22081 : checkPrefixCuts (2^48) 2898132993 9 Manual.Count131072.C022081.packed 128 cuts22081 = true := by
 decide +kernel
def pointBounds22081 : List (Nat × Nat × Nat) := [(2898134016,101300696346861,101301077458272),(2898225152,101301103770559,101301484882208)]
theorem point_links_checked22081 : (cuts22081.take 2).map (fun c => (2898132993-1+2*2^9*c.k,101300692364825+c.lower,101301073476234+c.upper)) = pointBounds22081 := by
 decide +kernel
def cuts22082 : List PrefixCut := [⟨51,233179286,233179418⟩,
⟨128,575510969,575511300⟩]
theorem checked22082 : checkPrefixCuts (2^48) 2898264065 9 Manual.Count131072.C022082.packed 128 cuts22082 = true := by
 decide +kernel
def pointBounds22082 : List (Nat × Nat × Nat) := [(2898316288,101301512055587,101301893167467)]
theorem point_links_checked22082 : (cuts22082.take 1).map (fun c => (2898264065-1+2*2^9*c.k,101301278876301+c.lower,101301659988049+c.upper)) = pointBounds22082 := by
 decide +kernel
def cuts22083 : List PrefixCut := [⟨12,54383752,54383785⟩,
⟨101,466915992,466916263⟩,
⟨128,585293224,585293562⟩]
theorem checked22083 : checkPrefixCuts (2^48) 2898395137 9 Manual.Count131072.C022083.packed 128 cuts22083 = true := by
 decide +kernel
def pointBounds22083 : List (Nat × Nat × Nat) := [(2898407424,101301908771022,101302289883134),(2898498560,101302321303262,101302702415612)]
theorem point_links_checked22083 : (cuts22083.take 2).map (fun c => (2898395137-1+2*2^9*c.k,101301854387270+c.lower,101302235499349+c.upper)) = pointBounds22083 := by
 decide +kernel
def cuts22084 : List PrefixCut := [⟨62,280643822,280643976⟩,
⟨128,576818360,576818683⟩]
theorem checked22084 : checkPrefixCuts (2^48) 2898526209 9 Manual.Count131072.C022084.packed 128 cuts22084 = true := by
 decide +kernel
def pointBounds22084 : List (Nat × Nat × Nat) := [(2898589696,101302720324316,101303101436887)]
theorem point_links_checked22084 : (cuts22084.take 1).map (fun c => (2898526209-1+2*2^9*c.k,101302439680494+c.lower,101302820792911+c.upper)) = pointBounds22084 := by
 decide +kernel
def cuts22085 : List PrefixCut := [⟨23,105941421,105941483⟩,
⟨112,514550628,514550923⟩,
⟨128,587764889,587765230⟩]
theorem checked22085 : checkPrefixCuts (2^48) 2898657281 9 Manual.Count131072.C022085.packed 128 cuts22085 = true := by
 decide +kernel
def pointBounds22085 : List (Nat × Nat × Nat) := [(2898680832,101303122440275,101303503553077),(2898771968,101303531049482,101303912162517)]
theorem point_links_checked22085 : (cuts22085.take 2).map (fun c => (2898657281-1+2*2^9*c.k,101303016498854+c.lower,101303397611594+c.upper)) = pointBounds22085 := by
 decide +kernel
def cuts22086 : List PrefixCut := [⟨73,331983590,331983780⟩,
⟨128,579873332,579873663⟩]
theorem checked22086 : checkPrefixCuts (2^48) 2898788353 9 Manual.Count131072.C022086.packed 128 cuts22086 = true := by
 decide +kernel
def pointBounds22086 : List (Nat × Nat × Nat) := [(2898863104,101303936247333,101304317360604)]
theorem point_links_checked22086 : (cuts22086.take 1).map (fun c => (2898788353-1+2*2^9*c.k,101303604263743+c.lower,101303985376824+c.upper)) = pointBounds22086 := by
 decide +kernel
def cuts22087 : List PrefixCut := [⟨34,153217350,153217440⟩,
⟨123,557807233,557807559⟩,
⟨128,579167514,579167852⟩]
theorem checked22087 : checkPrefixCuts (2^48) 2898919425 9 Manual.Count131072.C022087.packed 128 cuts22087 = true := by
 decide +kernel
def pointBounds22087 : List (Nat × Nat × Nat) := [(2898954240,101304337354425,101304718467927),(2899045376,101304741944308,101305123058046)]
theorem point_links_checked22087 : (cuts22087.take 2).map (fun c => (2898919425-1+2*2^9*c.k,101304184137075+c.lower,101304565250487+c.upper)) = pointBounds22087 := by
 decide +kernel
def cuts22088 : List PrefixCut := [⟨84,385061602,385061824⟩,
⟨128,586811408,586811742⟩]
theorem checked22088 : checkPrefixCuts (2^48) 2899050497 9 Manual.Count131072.C022088.packed 128 cuts22088 = true := by
 decide +kernel
def pointBounds22088 : List (Nat × Nat × Nat) := [(2899136512,101305148366191,101305529480163)]
theorem point_links_checked22088 : (cuts22088.take 1).map (fun c => (2899050497-1+2*2^9*c.k,101304763304589+c.lower,101305144418339+c.upper)) = pointBounds22088 := by
 decide +kernel
def cuts22089 : List PrefixCut := [⟨45,206698090,206698210⟩,
⟨128,586396492,586396828⟩]
theorem checked22089 : checkPrefixCuts (2^48) 2899181569 9 Manual.Count131072.C022089.packed 128 cuts22089 = true := by
 decide +kernel
def pointBounds22089 : List (Nat × Nat × Nat) := [(2899227648,101305556814087,101305937928291)]
theorem point_links_checked22089 : (cuts22089.take 1).map (fun c => (2899181569-1+2*2^9*c.k,101305350115997+c.lower,101305731230081+c.upper)) = pointBounds22089 := by
 decide +kernel
def cuts22090 : List PrefixCut := [⟨6,25338718,25338734⟩,
⟨95,426965282,426965533⟩,
⟨128,586369816,586370155⟩]
theorem checked22090 : checkPrefixCuts (2^48) 2899312641 9 Manual.Count131072.C022090.packed 128 cuts22090 = true := by
 decide +kernel
def pointBounds22090 : List (Nat × Nat × Nat) := [(2899318784,101305961851207,101306342965643),(2899409920,101306363477771,101306744592442)]
theorem point_links_checked22090 : (cuts22090.take 2).map (fun c => (2899312641-1+2*2^9*c.k,101305936512489+c.lower,101306317626909+c.upper)) = pointBounds22090 := by
 decide +kernel
def cuts22091 : List PrefixCut := [⟨56,253664716,253664864⟩,
⟨128,584498943,584499281⟩]
theorem checked22091 : checkPrefixCuts (2^48) 2899443713 9 Manual.Count131072.C022091.packed 128 cuts22091 = true := by
 decide +kernel
def pointBounds22091 : List (Nat × Nat × Nat) := [(2899501056,101306776547021,101307157661928)]
theorem point_links_checked22091 : (cuts22091.take 1).map (fun c => (2899443713-1+2*2^9*c.k,101306522882305+c.lower,101306903997064+c.upper)) = pointBounds22091 := by
 decide +kernel
def cuts22092 : List PrefixCut := [⟨17,78630143,78630189⟩,
⟨106,488469962,488470236⟩,
⟨128,585055143,585055475⟩]
theorem checked22092 : checkPrefixCuts (2^48) 2899574785 9 Manual.Count131072.C022092.packed 128 cuts22092 = true := by
 decide +kernel
def pointBounds22092 : List (Nat × Nat × Nat) := [(2899592192,101307186011391,101307567126534),(2899683328,101307595851210,101307976966581)]
theorem point_links_checked22092 : (cuts22092.take 2).map (fun c => (2899574785-1+2*2^9*c.k,101307107381248+c.lower,101307488496345+c.upper)) = pointBounds22092 := by
 decide +kernel
def cuts22093 : List PrefixCut := [⟨67,307805836,307806013⟩,
⟨128,583087340,583087678⟩]
theorem checked22093 : checkPrefixCuts (2^48) 2899705857 9 Manual.Count131072.C022093.packed 128 cuts22093 = true := by
 decide +kernel
def pointBounds22093 : List (Nat × Nat × Nat) := [(2899774464,101308000242227,101308381357833)]
theorem point_links_checked22093 : (cuts22093.take 1).map (fun c => (2899705857-1+2*2^9*c.k,101307692436391+c.lower,101308073551820+c.upper)) = pointBounds22093 := by
 decide +kernel
def cuts22094 : List PrefixCut := [⟨28,128805630,128805709⟩,
⟨117,535791961,535792270⟩,
⟨128,585293363,585293698⟩]
theorem checked22094 : checkPrefixCuts (2^48) 2899836929 9 Manual.Count131072.C022094.packed 128 cuts22094 = true := by
 decide +kernel
def pointBounds22094 : List (Nat × Nat × Nat) := [(2899865600,101308404329361,101308785445207),(2899956736,101308811315692,101309192431768)]
theorem point_links_checked22094 : (cuts22094.take 2).map (fun c => (2899836929-1+2*2^9*c.k,101308275523731+c.lower,101308656639498+c.upper)) = pointBounds22094 := by
 decide +kernel
def cuts22095 : List PrefixCut := [⟨78,350677938,350678140⟩,
⟨128,579055060,579055397⟩]
theorem checked22095 : checkPrefixCuts (2^48) 2899968001 9 Manual.Count131072.C022095.packed 128 cuts22095 = true := by
 decide +kernel
def pointBounds22095 : List (Nat × Nat × Nat) := [(2900047872,101309211495032,101309592611336)]
theorem point_links_checked22095 : (cuts22095.take 1).map (fun c => (2899968001-1+2*2^9*c.k,101308860817094+c.lower,101309241933196+c.upper)) = pointBounds22095 := by
 decide +kernel
def cuts22096 : List PrefixCut := [⟨39,178971849,178971952⟩,
⟨128,589413817,589414148⟩]
theorem checked22096 : checkPrefixCuts (2^48) 2900099073 9 Manual.Count131072.C022096.packed 128 cuts22096 = true := by
 decide +kernel
def pointBounds22096 : List (Nat × Nat × Nat) := [(2900139008,101309618844003,101309999960545),(2900230144,101310029285971,101310410402741)]
theorem point_links_checked22096 : (cuts22096.take 2).map (fun c => (2900099073-1+2*2^9*c.k,101309439872154+c.lower,101309820988593+c.upper)) = pointBounds22096 := by
 decide +kernel
def cuts22097 : List PrefixCut := [⟨89,403829535,403829764⟩,
⟨128,582302455,582302786⟩]
theorem checked22097 : checkPrefixCuts (2^48) 2900230145 9 Manual.Count131072.C022097.packed 128 cuts22097 = true := by
 decide +kernel
def pointBounds22097 : List (Nat × Nat × Nat) := [(2900321280,101310433115506,101310814232505)]
theorem point_links_checked22097 : (cuts22097.take 1).map (fun c => (2900230145-1+2*2^9*c.k,101310029285971+c.lower,101310410402741+c.upper)) = pointBounds22097 := by
 decide +kernel
def cuts22098 : List PrefixCut := [⟨50,236407393,236407529⟩,
⟨128,593339525,593339866⟩]
theorem checked22098 : checkPrefixCuts (2^48) 2900361217 9 Manual.Count131072.C022098.packed 128 cuts22098 = true := by
 decide +kernel
def pointBounds22098 : List (Nat × Nat × Nat) := [(2900412416,101310847995819,101311229113056)]
theorem point_links_checked22098 : (cuts22098.take 1).map (fun c => (2900361217-1+2*2^9*c.k,101310611588426+c.lower,101310992705527+c.upper)) = pointBounds22098 := by
 decide +kernel
def cuts22099 : List PrefixCut := [⟨11,51918351,51918380⟩,
⟨100,464540646,464540905⟩,
⟨128,590886636,590886966⟩]
theorem checked22099 : checkPrefixCuts (2^48) 2900492289 9 Manual.Count131072.C022099.packed 128 cuts22099 = true := by
 decide +kernel
def pointBounds22099 : List (Nat × Nat × Nat) := [(2900503552,101311256846302,101311637963773),(2900594688,101311669468597,101312050586298)]
theorem point_links_checked22099 : (cuts22099.take 2).map (fun c => (2900492289-1+2*2^9*c.k,101311204927951+c.lower,101311586045393+c.upper)) = pointBounds22099 := by
 decide +kernel
def cuts22100 : List PrefixCut := [⟨61,272386803,272386965⟩,
⟨128,576401271,576401605⟩]
theorem checked22100 : checkPrefixCuts (2^48) 2900623361 9 Manual.Count131072.C022100.packed 128 cuts22100 = true := by
 decide +kernel
def pointBounds22100 : List (Nat × Nat × Nat) := [(2900685824,101312068201390,101312449319324)]
theorem point_links_checked22100 : (cuts22100.take 1).map (fun c => (2900623361-1+2*2^9*c.k,101311795814587+c.lower,101312176932359+c.upper)) = pointBounds22100 := by
 decide +kernel
def cuts22101 : List PrefixCut := [⟨22,99557585,99557639⟩,
⟨111,502437743,502438031⟩,
⟨128,579189243,579189575⟩]
theorem checked22101 : checkPrefixCuts (2^48) 2900754433 9 Manual.Count131072.C022101.packed 128 cuts22101 = true := by
 decide +kernel
def pointBounds22101 : List (Nat × Nat × Nat) := [(2900776960,101312471773443,101312852891603),(2900868096,101312874653601,101313255771995)]
theorem point_links_checked22101 : (cuts22101.take 2).map (fun c => (2900754433-1+2*2^9*c.k,101312372215858+c.lower,101312753333964+c.upper)) = pointBounds22101 := by
 decide +kernel
def cuts22102 : List PrefixCut := [⟨72,329997242,329997435⟩,
⟨128,591388647,591388988⟩]
theorem checked22102 : checkPrefixCuts (2^48) 2900885505 9 Manual.Count131072.C022102.packed 128 cuts22102 = true := by
 decide +kernel
def pointBounds22102 : List (Nat × Nat × Nat) := [(2900959232,101313281402343,101313662520974)]
theorem point_links_checked22102 : (cuts22102.take 1).map (fun c => (2900885505-1+2*2^9*c.k,101312951405101+c.lower,101313332523539+c.upper)) = pointBounds22102 := by
 decide +kernel
def cuts22103 : List PrefixCut := [⟨33,151651199,151651288⟩,
⟨122,551873670,551873988⟩,
⟨128,580204098,580204433⟩]
theorem checked22103 : checkPrefixCuts (2^48) 2901016577 9 Manual.Count131072.C022103.packed 128 cuts22103 = true := by
 decide +kernel
def pointBounds22103 : List (Nat × Nat × Nat) := [(2901050368,101313694444947,101314075563815),(2901141504,101314094667418,101314475786515)]
theorem point_links_checked22103 : (cuts22103.take 2).map (fun c => (2901016577-1+2*2^9*c.k,101313542793748+c.lower,101313923912527+c.upper)) = pointBounds22103 := by
 decide +kernel
def cuts22104 : List PrefixCut := [⟨83,377021631,377021850⟩,
⟨128,585222914,585223254⟩]
theorem checked22104 : checkPrefixCuts (2^48) 2901147649 9 Manual.Count131072.C022104.packed 128 cuts22104 = true := by
 decide +kernel
def pointBounds22104 : List (Nat × Nat × Nat) := [(2901232640,101314500019477,101314881138810)]
theorem point_links_checked22104 : (cuts22104.take 1).map (fun c => (2901147649-1+2*2^9*c.k,101314122997846+c.lower,101314504116960+c.upper)) = pointBounds22104 := by
 decide +kernel
def cuts22105 : List PrefixCut := [⟨44,202862090,202862206⟩,
⟨128,581218982,581219314⟩]
theorem checked22105 : checkPrefixCuts (2^48) 2901278721 9 Manual.Count131072.C022105.packed 128 cuts22105 = true := by
 decide +kernel
def pointBounds22105 : List (Nat × Nat × Nat) := [(2901323776,101314911082850,101315292202420)]
theorem point_links_checked22105 : (cuts22105.take 1).map (fun c => (2901278721-1+2*2^9*c.k,101314708220760+c.lower,101315089340214+c.upper)) = pointBounds22105 := by
 decide +kernel
def cuts22106 : List PrefixCut := [⟨5,22992095,22992108⟩,
⟨94,432186367,432186616⟩,
⟨128,586625244,586625582⟩]
theorem checked22106 : checkPrefixCuts (2^48) 2901409793 9 Manual.Count131072.C022106.packed 128 cuts22106 = true := by
 decide +kernel
def pointBounds22106 : List (Nat × Nat × Nat) := [(2901414912,101315312431837,101315693551636),(2901506048,101315721626109,101316102746144)]
theorem point_links_checked22106 : (cuts22106.take 2).map (fun c => (2901409793-1+2*2^9*c.k,101315289439742+c.lower,101315670559528+c.upper)) = pointBounds22106 := by
 decide +kernel
def cuts22107 : List PrefixCut := [⟨55,252414349,252414491⟩,
⟨128,585240687,585241022⟩]
theorem checked22107 : checkPrefixCuts (2^48) 2901540865 9 Manual.Count131072.C022107.packed 128 cuts22107 = true := by
 decide +kernel
def pointBounds22107 : List (Nat × Nat × Nat) := [(2901597184,101316128479335,101316509599601)]
theorem point_links_checked22107 : (cuts22107.take 1).map (fun c => (2901540865-1+2*2^9*c.k,101315876064986+c.lower,101316257185110+c.upper)) = pointBounds22107 := by
 decide +kernel
def cuts22108 : List PrefixCut := [⟨16,74693164,74693207⟩,
⟨105,485691925,485692196⟩,
⟨128,588512346,588512675⟩]
theorem checked22108 : checkPrefixCuts (2^48) 2901671937 9 Manual.Count131072.C022108.packed 128 cuts22108 = true := by
 decide +kernel
def pointBounds22108 : List (Nat × Nat × Nat) := [(2901688320,101316535998837,101316917119339),(2901779456,101316946997598,101317328118328)]
theorem point_links_checked22108 : (cuts22108.take 2).map (fun c => (2901671937-1+2*2^9*c.k,101316461305673+c.lower,101316842426132+c.upper)) = pointBounds22108 := by
 decide +kernel
def cuts22109 : List PrefixCut := [⟨66,304188449,304188618⟩,
⟨128,585381838,585382166⟩]
theorem checked22109 : checkPrefixCuts (2^48) 2901803009 9 Manual.Count131072.C022109.packed 128 cuts22109 = true := by
 decide +kernel
def pointBounds22109 : List (Nat × Nat × Nat) := [(2901870592,101317354006468,101317735127425)]
theorem point_links_checked22109 : (cuts22109.take 1).map (fun c => (2901803009-1+2*2^9*c.k,101317049818019+c.lower,101317430938807+c.upper)) = pointBounds22109 := by
 decide +kernel
def cuts22110 : List PrefixCut := [⟨27,122698875,122698948⟩,
⟨116,521728811,521729119⟩,
⟨128,576238000,576238339⟩]
theorem checked22110 : checkPrefixCuts (2^48) 2901934081 9 Manual.Count131072.C022110.packed 128 cuts22110 = true := by
 decide +kernel
def pointBounds22110 : List (Nat × Nat × Nat) := [(2901961728,101317757898732,101318139019921),(2902052864,101318156928668,101318538050092)]
theorem point_links_checked22110 : (cuts22110.take 2).map (fun c => (2901934081-1+2*2^9*c.k,101317635199857+c.lower,101318016320973+c.upper)) = pointBounds22110 := by
 decide +kernel
def cuts22111 : List PrefixCut := [⟨77,349745673,349745873⟩,
⟨128,584068025,584068357⟩]
theorem checked22111 : checkPrefixCuts (2^48) 2902065153 9 Manual.Count131072.C022111.packed 128 cuts22111 = true := by
 decide +kernel
def pointBounds22111 : List (Nat × Nat × Nat) := [(2902144000,101318561183530,101318942305185)]
theorem point_links_checked22111 : (cuts22111.take 1).map (fun c => (2902065153-1+2*2^9*c.k,101318211437857+c.lower,101318592559312+c.upper)) = pointBounds22111 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000065
