import PlattAssemblyKernel
import PlattCertificates.Count131072.C030128
import PlattCertificates.Count131072.C030129
import PlattCertificates.Count131072.C030130
import PlattCertificates.Count131072.C030131
import PlattCertificates.Count131072.C030132
import PlattCertificates.Count131072.C030133
import PlattCertificates.Count131072.C030134
import PlattCertificates.Count131072.C030135
import PlattCertificates.Count131072.C030136
import PlattCertificates.Count131072.C030137
import PlattCertificates.Count131072.C030138
import PlattCertificates.Count131072.C030139
import PlattCertificates.Count131072.C030140
import PlattCertificates.Count131072.C030141
import PlattCertificates.Count131072.C030142
import PlattCertificates.Count131072.C030143
import PlattCertificates.Count131072.C030144
import PlattCertificates.Count131072.C030145
import PlattCertificates.Count131072.C030146
import PlattCertificates.Count131072.C030147
import PlattCertificates.Count131072.C030148
import PlattCertificates.Count131072.C030149
import PlattCertificates.Count131072.C030150
import PlattCertificates.Count131072.C030151
import PlattCertificates.Count131072.C030152
import PlattCertificates.Count131072.C030153
import PlattCertificates.Count131072.C030154
import PlattCertificates.Count131072.C030155
import PlattCertificates.Count131072.C030156
import PlattCertificates.Count131072.C030157
import PlattCertificates.Count131072.C030158
import PlattCertificates.Count131072.C030159
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30128 : List PrefixCut := [⟨76,252713762,252713902⟩,
⟨128,419050648,419050884⟩]
theorem checked30128 : checkPrefixCuts (2^48) 3952869377 9 Manual.Count131072.C030128.packed 128 cuts30128 = true := by
 decide +kernel
def pointBounds30128 : List (Nat × Nat × Nat) := [(3952947200,105282437523953,105282820875829)]
theorem point_links_checked30128 : (cuts30128.take 1).map (fun c => (3952869377-1+2*2^9*c.k,105282184810191+c.lower,105282568161927+c.upper)) = pointBounds30128 := by
 decide +kernel
def cuts30129 : List PrefixCut := [⟨69,227499170,227499298⟩,
⟨128,420389623,420389860⟩]
theorem checked30129 : checkPrefixCuts (2^48) 3953000449 9 Manual.Count131072.C030129.packed 128 cuts30129 = true := by
 decide +kernel
def pointBounds30129 : List (Nat × Nat × Nat) := [(3953071104,105282831360009,105283214712109)]
theorem point_links_checked30129 : (cuts30129.take 1).map (fun c => (3953000449-1+2*2^9*c.k,105282603860839+c.lower,105282987212811+c.upper)) = pointBounds30129 := by
 decide +kernel
def cuts30130 : List PrefixCut := [⟨62,206344703,206344819⟩,
⟨128,424790184,424790422⟩]
theorem checked30130 : checkPrefixCuts (2^48) 3953131521 9 Manual.Count131072.C030130.packed 128 cuts30130 = true := by
 decide +kernel
def pointBounds30130 : List (Nat × Nat × Nat) := [(3953195008,105283230595165,105283613947490)]
theorem point_links_checked30130 : (cuts30130.take 1).map (fun c => (3953131521-1+2*2^9*c.k,105283024250462+c.lower,105283407602671+c.upper)) = pointBounds30130 := by
 decide +kernel
def cuts30131 : List PrefixCut := [⟨55,180990795,180990900⟩,
⟨128,430899216,430899459⟩]
theorem checked30131 : checkPrefixCuts (2^48) 3953262593 9 Manual.Count131072.C030131.packed 128 cuts30131 = true := by
 decide +kernel
def pointBounds30131 : List (Nat × Nat × Nat) := [(3953318912,105283630031441,105284013383993)]
theorem point_links_checked30131 : (cuts30131.take 1).map (fun c => (3953262593-1+2*2^9*c.k,105283449040646+c.lower,105283832393093+c.upper)) = pointBounds30131 := by
 decide +kernel
def cuts30132 : List PrefixCut := [⟨48,155567313,155567404⟩,
⟨128,418069465,418069704⟩]
theorem checked30132 : checkPrefixCuts (2^48) 3953393665 9 Manual.Count131072.C030132.packed 128 cuts30132 = true := by
 decide +kernel
def pointBounds30132 : List (Nat × Nat × Nat) := [(3953442816,105284035507175,105284418859956)]
theorem point_links_checked30132 : (cuts30132.take 1).map (fun c => (3953393665-1+2*2^9*c.k,105283879939862+c.lower,105284263292552+c.upper)) = pointBounds30132 := by
 decide +kernel
def cuts30133 : List PrefixCut := [⟨41,133918847,133918923⟩,
⟨128,420974577,420974812⟩]
theorem checked30133 : checkPrefixCuts (2^48) 3953524737 9 Manual.Count131072.C030133.packed 128 cuts30133 = true := by
 decide +kernel
def pointBounds30133 : List (Nat × Nat × Nat) := [(3953566720,105284431928174,105284815281179)]
theorem point_links_checked30133 : (cuts30133.take 1).map (fun c => (3953524737-1+2*2^9*c.k,105284298009327+c.lower,105284681362256+c.upper)) = pointBounds30133 := by
 decide +kernel
def cuts30134 : List PrefixCut := [⟨34,114692355,114692419⟩,
⟨128,422954033,422954276⟩]
theorem checked30134 : checkPrefixCuts (2^48) 3953655809 9 Manual.Count131072.C030134.packed 128 cuts30134 = true := by
 decide +kernel
def pointBounds30134 : List (Nat × Nat × Nat) := [(3953690624,105284833676259,105285217029487)]
theorem point_links_checked30134 : (cuts30134.take 1).map (fun c => (3953655809-1+2*2^9*c.k,105284718983904+c.lower,105285102337068+c.upper)) = pointBounds30134 := by
 decide +kernel
def cuts30135 : List PrefixCut := [⟨27,88205611,88205661⟩,
⟨128,418597435,418597674⟩]
theorem checked30135 : checkPrefixCuts (2^48) 3953786881 9 Manual.Count131072.C030135.packed 128 cuts30135 = true := by
 decide +kernel
def pointBounds30135 : List (Nat × Nat × Nat) := [(3953814528,105285230143548,105285613497005)]
theorem point_links_checked30135 : (cuts30135.take 1).map (fun c => (3953786881-1+2*2^9*c.k,105285141937937+c.lower,105285525291344+c.upper)) = pointBounds30135 := by
 decide +kernel
def cuts30136 : List PrefixCut := [⟨20,68269938,68269975⟩,
⟨128,424065000,424065235⟩]
theorem checked30136 : checkPrefixCuts (2^48) 3953917953 9 Manual.Count131072.C030136.packed 128 cuts30136 = true := by
 decide +kernel
def pointBounds30136 : List (Nat × Nat × Nat) := [(3953938432,105285628805310,105286012158993)]
theorem point_links_checked30136 : (cuts30136.take 1).map (fun c => (3953917953-1+2*2^9*c.k,105285560535372+c.lower,105285943889018+c.upper)) = pointBounds30136 := by
 decide +kernel
def cuts30137 : List PrefixCut := [⟨13,42071150,42071172⟩,
⟨128,423267932,423268162⟩]
theorem checked30137 : checkPrefixCuts (2^48) 3954049025 9 Manual.Count131072.C030137.packed 128 cuts30137 = true := by
 decide +kernel
def pointBounds30137 : List (Nat × Nat × Nat) := [(3954062336,105286026671522,105286410025425)]
theorem point_links_checked30137 : (cuts30137.take 1).map (fun c => (3954049025-1+2*2^9*c.k,105285984600372+c.lower,105286367954253+c.upper)) = pointBounds30137 := by
 decide +kernel
def cuts30138 : List PrefixCut := [⟨6,19362069,19362080⟩,
⟨127,418769379,418769614⟩,
⟨128,422542014,422542251⟩]
theorem checked30138 : checkPrefixCuts (2^48) 3954180097 9 Manual.Count131072.C030138.packed 128 cuts30138 = true := by
 decide +kernel
def pointBounds30138 : List (Nat × Nat × Nat) := [(3954186240,105286427230373,105286810584495),(3954310144,105286826637683,105287209992029)]
theorem point_links_checked30138 : (cuts30138.take 2).map (fun c => (3954180097-1+2*2^9*c.k,105286407868304+c.lower,105286791222415+c.upper)) = pointBounds30138 := by
 decide +kernel
def cuts30139 : List PrefixCut := [⟨120,395622197,395622421⟩,
⟨128,422812764,422813002⟩]
theorem checked30139 : checkPrefixCuts (2^48) 3954311169 9 Manual.Count131072.C030139.packed 128 cuts30139 = true := by
 decide +kernel
def pointBounds30139 : List (Nat × Nat × Nat) := [(3954434048,105287226032515,105287609387087)]
theorem point_links_checked30139 : (cuts30139.take 1).map (fun c => (3954311169-1+2*2^9*c.k,105286830410318+c.lower,105287213764666+c.upper)) = pointBounds30139 := by
 decide +kernel
def cuts30140 : List PrefixCut := [⟨113,376462413,376462628⟩,
⟨128,425005262,425005506⟩]
theorem checked30140 : checkPrefixCuts (2^48) 3954442241 9 Manual.Count131072.C030140.packed 128 cuts30140 = true := by
 decide +kernel
def pointBounds30140 : List (Nat × Nat × Nat) := [(3954557952,105287629685495,105288013040296)]
theorem point_links_checked30140 : (cuts30140.take 1).map (fun c => (3954442241-1+2*2^9*c.k,105287253223082+c.lower,105287636577668+c.upper)) = pointBounds30140 := by
 decide +kernel
def cuts30141 : List PrefixCut := [⟨106,355311043,355311236⟩,
⟨128,429546461,429546696⟩]
theorem checked30141 : checkPrefixCuts (2^48) 3954573313 9 Manual.Count131072.C030141.packed 128 cuts30141 = true := by
 decide +kernel
def pointBounds30141 : List (Nat × Nat × Nat) := [(3954681856,105288033539387,105288416894410)]
theorem point_links_checked30141 : (cuts30141.take 1).map (fun c => (3954573313-1+2*2^9*c.k,105287678228344+c.lower,105288061583174+c.upper)) = pointBounds30141 := by
 decide +kernel
def cuts30142 : List PrefixCut := [⟨99,327185896,327186081⟩,
⟨128,421276087,421276321⟩]
theorem checked30142 : checkPrefixCuts (2^48) 3954704385 9 Manual.Count131072.C030142.packed 128 cuts30142 = true := by
 decide +kernel
def pointBounds30142 : List (Nat × Nat × Nat) := [(3954805760,105288434960701,105288818315951)]
theorem point_links_checked30142 : (cuts30142.take 1).map (fun c => (3954704385-1+2*2^9*c.k,105288107774805+c.lower,105288491129870+c.upper)) = pointBounds30142 := by
 decide +kernel
def cuts30143 : List PrefixCut := [⟨92,302407669,302407841⟩,
⟨128,421973794,421974032⟩]
theorem checked30143 : checkPrefixCuts (2^48) 3954835457 9 Manual.Count131072.C030143.packed 128 cuts30143 = true := by
 decide +kernel
def pointBounds30143 : List (Nat × Nat × Nat) := [(3954929664,105288831458561,105289214814032)]
theorem point_links_checked30143 : (cuts30143.take 1).map (fun c => (3954835457-1+2*2^9*c.k,105288529050892+c.lower,105288912406191+c.upper)) = pointBounds30143 := by
 decide +kernel
def cuts30144 : List PrefixCut := [⟨85,276919378,276919536⟩,
⟨128,418259055,418259291⟩]
theorem checked30144 : checkPrefixCuts (2^48) 3954966529 9 Manual.Count131072.C030144.packed 128 cuts30144 = true := by
 decide +kernel
def pointBounds30144 : List (Nat × Nat × Nat) := [(3955053568,105289227944064,105289611299759)]
theorem point_links_checked30144 : (cuts30144.take 1).map (fun c => (3954966529-1+2*2^9*c.k,105288951024686+c.lower,105289334380223+c.upper)) = pointBounds30144 := by
 decide +kernel
def cuts30145 : List PrefixCut := [⟨78,253354205,253354353⟩,
⟨128,417533533,417533774⟩]
theorem checked30145 : checkPrefixCuts (2^48) 3955097601 9 Manual.Count131072.C030145.packed 128 cuts30145 = true := by
 decide +kernel
def pointBounds30145 : List (Nat × Nat × Nat) := [(3955177472,105289622637946,105290005993867)]
theorem point_links_checked30145 : (cuts30145.take 1).map (fun c => (3955097601-1+2*2^9*c.k,105289369283741+c.lower,105289752639514+c.upper)) = pointBounds30145 := by
 decide +kernel
def cuts30146 : List PrefixCut := [⟨71,235270172,235270304⟩,
⟨128,423355113,423355350⟩]
theorem checked30146 : checkPrefixCuts (2^48) 3955228673 9 Manual.Count131072.C030146.packed 128 cuts30146 = true := by
 decide +kernel
def pointBounds30146 : List (Nat × Nat × Nat) := [(3955301376,105290022087446,105290405443592)]
theorem point_links_checked30146 : (cuts30146.take 1).map (fun c => (3955228673-1+2*2^9*c.k,105289786817274+c.lower,105290170173288+c.upper)) = pointBounds30146 := by
 decide +kernel
def cuts30147 : List PrefixCut := [⟨64,207651646,207651765⟩,
⟨128,415299846,415300078⟩]
theorem checked30147 : checkPrefixCuts (2^48) 3955359745 9 Manual.Count131072.C030147.packed 128 cuts30147 = true := by
 decide +kernel
def pointBounds30147 : List (Nat × Nat × Nat) := [(3955425280,105290417824033,105290801180403)]
theorem point_links_checked30147 : (cuts30147.take 1).map (fun c => (3955359745-1+2*2^9*c.k,105290210172387+c.lower,105290593528638+c.upper)) = pointBounds30147 := by
 decide +kernel
def cuts30148 : List PrefixCut := [⟨57,191420457,191420566⟩,
⟨128,427027396,427027644⟩]
theorem checked30148 : checkPrefixCuts (2^48) 3955490817 9 Manual.Count131072.C030148.packed 128 cuts30148 = true := by
 decide +kernel
def pointBounds30148 : List (Nat × Nat × Nat) := [(3955549184,105290816892690,105291200249282)]
theorem point_links_checked30148 : (cuts30148.take 1).map (fun c => (3955490817-1+2*2^9*c.k,105290625472233+c.lower,105291008828716+c.upper)) = pointBounds30148 := by
 decide +kernel
def cuts30149 : List PrefixCut := [⟨50,168145717,168145814⟩,
⟨128,424807386,424807626⟩]
theorem checked30149 : checkPrefixCuts (2^48) 3955621889 9 Manual.Count131072.C030149.packed 128 cuts30149 = true := by
 decide +kernel
def pointBounds30149 : List (Nat × Nat × Nat) := [(3955673088,105291220645346,105291604002174)]
theorem point_links_checked30149 : (cuts30149.take 1).map (fun c => (3955621889-1+2*2^9*c.k,105291052499629+c.lower,105291435856360+c.upper)) = pointBounds30149 := by
 decide +kernel
def cuts30150 : List PrefixCut := [⟨43,140603142,140603219⟩,
⟨128,421591293,421591524⟩]
theorem checked30150 : checkPrefixCuts (2^48) 3955752961 9 Manual.Count131072.C030150.packed 128 cuts30150 = true := by
 decide +kernel
def pointBounds30150 : List (Nat × Nat × Nat) := [(3955796992,105291617910157,105292001267205)]
theorem point_links_checked30150 : (cuts30150.take 1).map (fun c => (3955752961-1+2*2^9*c.k,105291477307015+c.lower,105291860663986+c.upper)) = pointBounds30150 := by
 decide +kernel
def cuts30151 : List PrefixCut := [⟨36,116406544,116406610⟩,
⟨128,419371617,419371856⟩]
theorem checked30151 : checkPrefixCuts (2^48) 3955884033 9 Manual.Count131072.C030151.packed 128 cuts30151 = true := by
 decide +kernel
def pointBounds30151 : List (Nat × Nat × Nat) := [(3955920896,105292015304852,105292398662120)]
theorem point_links_checked30151 : (cuts30151.take 1).map (fun c => (3955884033-1+2*2^9*c.k,105291898898308+c.lower,105292282255510+c.upper)) = pointBounds30151 := by
 decide +kernel
def cuts30152 : List PrefixCut := [⟨29,93919114,93919165⟩,
⟨128,423769004,423769240⟩]
theorem checked30152 : checkPrefixCuts (2^48) 3956015105 9 Manual.Count131072.C030152.packed 128 cuts30152 = true := by
 decide +kernel
def pointBounds30152 : List (Nat × Nat × Nat) := [(3956044800,105292412189039,105292795546531)]
theorem point_links_checked30152 : (cuts30152.take 1).map (fun c => (3956015105-1+2*2^9*c.k,105292318269925+c.lower,105292701627366+c.upper)) = pointBounds30152 := by
 decide +kernel
def cuts30153 : List PrefixCut := [⟨22,73354162,73354203⟩,
⟨128,419913039,419913272⟩]
theorem checked30153 : checkPrefixCuts (2^48) 3956146177 9 Manual.Count131072.C030153.packed 128 cuts30153 = true := by
 decide +kernel
def pointBounds30153 : List (Nat × Nat × Nat) := [(3956168704,105292815393091,105293198750809)]
theorem point_links_checked30153 : (cuts30153.take 1).map (fun c => (3956146177-1+2*2^9*c.k,105292742038929+c.lower,105293125396606+c.upper)) = pointBounds30153 := by
 decide +kernel
def cuts30154 : List PrefixCut := [⟨15,49162068,49162094⟩,
⟨128,426515618,426515855⟩]
theorem checked30154 : checkPrefixCuts (2^48) 3956277249 9 Manual.Count131072.C030154.packed 128 cuts30154 = true := by
 decide +kernel
def pointBounds30154 : List (Nat × Nat × Nat) := [(3956292608,105293211114036,105293594471972)]
theorem point_links_checked30154 : (cuts30154.take 1).map (fun c => (3956277249-1+2*2^9*c.k,105293161951968+c.lower,105293545309878+c.upper)) = pointBounds30154 := by
 decide +kernel
def cuts30155 : List PrefixCut := [⟨8,26323268,26323282⟩,
⟨128,417537450,417537687⟩]
theorem checked30155 : checkPrefixCuts (2^48) 3956408321 9 Manual.Count131072.C030155.packed 128 cuts30155 = true := by
 decide +kernel
def pointBounds30155 : List (Nat × Nat × Nat) := [(3956416512,105293614790854,105293998149015)]
theorem point_links_checked30155 : (cuts30155.take 1).map (fun c => (3956408321-1+2*2^9*c.k,105293588467586+c.lower,105293971825733+c.upper)) = pointBounds30155 := by
 decide +kernel
def cuts30156 : List PrefixCut := [⟨1,3201376,3201377⟩,
⟨122,400877114,400877341⟩,
⟨128,420653863,420654102⟩]
theorem checked30156 : checkPrefixCuts (2^48) 3956539393 9 Manual.Count131072.C030156.packed 128 cuts30156 = true := by
 decide +kernel
def pointBounds30156 : List (Nat × Nat × Nat) := [(3956540416,105294009206412,105294392564797),(3956664320,105294406882150,105294790240761)]
theorem point_links_checked30156 : (cuts30156.take 2).map (fun c => (3956539393-1+2*2^9*c.k,105294006005036+c.lower,105294389363420+c.upper)) = pointBounds30156 := by
 decide +kernel
def cuts30157 : List PrefixCut := [⟨115,380162943,380163158⟩,
⟨128,424339078,424339318⟩]
theorem checked30157 : checkPrefixCuts (2^48) 3956670465 9 Manual.Count131072.C030157.packed 128 cuts30157 = true := by
 decide +kernel
def pointBounds30157 : List (Nat × Nat × Nat) := [(3956788224,105294806821842,105295190180680)]
theorem point_links_checked30157 : (cuts30157.take 1).map (fun c => (3956670465-1+2*2^9*c.k,105294426658899+c.lower,105294810017522+c.upper)) = pointBounds30157 := by
 decide +kernel
def cuts30158 : List PrefixCut := [⟨108,350700362,350700560⟩,
⟨128,417140265,417140501⟩]
theorem checked30158 : checkPrefixCuts (2^48) 3956801537 9 Manual.Count131072.C030158.packed 128 cuts30158 = true := by
 decide +kernel
def pointBounds30158 : List (Nat × Nat × Nat) := [(3956912128,105295201698339,105295585057400)]
theorem point_links_checked30158 : (cuts30158.take 1).map (fun c => (3956801537-1+2*2^9*c.k,105294850997977+c.lower,105295234356840+c.upper)) = pointBounds30158 := by
 decide +kernel
def cuts30159 : List PrefixCut := [⟨101,335110794,335110982⟩,
⟨128,422319253,422319486⟩]
theorem checked30159 : checkPrefixCuts (2^48) 3956932609 9 Manual.Count131072.C030159.packed 128 cuts30159 = true := by
 decide +kernel
def pointBounds30159 : List (Nat × Nat × Nat) := [(3957036032,105295603249036,105295986608323)]
theorem point_links_checked30159 : (cuts30159.take 1).map (fun c => (3956932609-1+2*2^9*c.k,105295268138242+c.lower,105295651497341+c.upper)) = pointBounds30159 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000004
