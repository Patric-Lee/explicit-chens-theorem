import PlattAssemblyKernel
import PlattCertificates.Count131072.C022112
import PlattCertificates.Count131072.C022113
import PlattCertificates.Count131072.C022114
import PlattCertificates.Count131072.C022115
import PlattCertificates.Count131072.C022116
import PlattCertificates.Count131072.C022117
import PlattCertificates.Count131072.C022118
import PlattCertificates.Count131072.C022119
import PlattCertificates.Count131072.C022120
import PlattCertificates.Count131072.C022121
import PlattCertificates.Count131072.C022122
import PlattCertificates.Count131072.C022123
import PlattCertificates.Count131072.C022124
import PlattCertificates.Count131072.C022125
import PlattCertificates.Count131072.C022126
import PlattCertificates.Count131072.C022127
import PlattCertificates.Count131072.C022128
import PlattCertificates.Count131072.C022129
import PlattCertificates.Count131072.C022130
import PlattCertificates.Count131072.C022131
import PlattCertificates.Count131072.C022132
import PlattCertificates.Count131072.C022133
import PlattCertificates.Count131072.C022134
import PlattCertificates.Count131072.C022135
import PlattCertificates.Count131072.C022136
import PlattCertificates.Count131072.C022137
import PlattCertificates.Count131072.C022138
import PlattCertificates.Count131072.C022139
import PlattCertificates.Count131072.C022140
import PlattCertificates.Count131072.C022141
import PlattCertificates.Count131072.C022142
import PlattCertificates.Count131072.C022143
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts22112 : List PrefixCut := [⟨38,167398202,167398297⟩,
⟨127,575313063,575313387⟩,
⟨128,579289345,579289672⟩]
theorem checked22112 : checkPrefixCuts (2^48) 2902196225 9 Manual.Count131072.C022112.packed 128 cuts22112 = true := by
 decide +kernel
def pointBounds22112 : List (Nat × Nat × Nat) := [(2902235136,101318962904084,101319344025966),(2902326272,101319370818945,101319751941056)]
theorem point_links_checked22112 : (cuts22112.take 2).map (fun c => (2902196225-1+2*2^9*c.k,101318795505882+c.lower,101319176627669+c.upper)) = pointBounds22112 := by
 decide +kernel
def cuts22113 : List PrefixCut := [⟨88,397524968,397525196⟩,
⟨128,578002476,578002808⟩]
theorem checked22113 : checkPrefixCuts (2^48) 2902327297 9 Manual.Count131072.C022113.packed 128 cuts22113 = true := by
 decide +kernel
def pointBounds22113 : List (Nat × Nat × Nat) := [(2902417408,101319772320195,101320153442537)]
theorem point_links_checked22113 : (cuts22113.take 1).map (fun c => (2902327297-1+2*2^9*c.k,101319374795227+c.lower,101319755917341+c.upper)) = pointBounds22113 := by
 decide +kernel
def cuts22114 : List PrefixCut := [⟨49,228187524,228187655⟩,
⟨128,587383209,587383548⟩]
theorem checked22114 : checkPrefixCuts (2^48) 2902458369 9 Manual.Count131072.C022114.packed 128 cuts22114 = true := by
 decide +kernel
def pointBounds22114 : List (Nat × Nat × Nat) := [(2902508544,101320180985227,101320562107804)]
theorem point_links_checked22114 : (cuts22114.take 1).map (fun c => (2902458369-1+2*2^9*c.k,101319952797703+c.lower,101320333920149+c.upper)) = pointBounds22114 := by
 decide +kernel
def cuts22115 : List PrefixCut := [⟨10,47129146,47129173⟩,
⟨99,457610980,457611244⟩,
⟨128,595599066,595599405⟩]
theorem checked22115 : checkPrefixCuts (2^48) 2902589441 9 Manual.Count131072.C022115.packed 128 cuts22115 = true := by
 decide +kernel
def pointBounds22115 : List (Nat × Nat × Nat) := [(2902599680,101320587310058,101320968432870),(2902690816,101320997791892,101321378914941)]
theorem point_links_checked22115 : (cuts22115.take 2).map (fun c => (2902589441-1+2*2^9*c.k,101320540180912+c.lower,101320921303697+c.upper)) = pointBounds22115 := by
 decide +kernel
def cuts22116 : List PrefixCut := [⟨60,275293042,275293195⟩,
⟨128,580445451,580445772⟩]
theorem checked22116 : checkPrefixCuts (2^48) 2902720513 9 Manual.Count131072.C022116.packed 128 cuts22116 = true := by
 decide +kernel
def pointBounds22116 : List (Nat × Nat × Nat) := [(2902781952,101321411073020,101321792196297)]
theorem point_links_checked22116 : (cuts22116.take 1).map (fun c => (2902720513-1+2*2^9*c.k,101321135779978+c.lower,101321516903102+c.upper)) = pointBounds22116 := by
 decide +kernel
def cuts22117 : List PrefixCut := [⟨21,94152629,94152682⟩,
⟨110,501589999,501590281⟩,
⟨128,582067543,582067869⟩]
theorem checked22117 : checkPrefixCuts (2^48) 2902851585 9 Manual.Count131072.C022117.packed 128 cuts22117 = true := by
 decide +kernel
def pointBounds22117 : List (Nat × Nat × Nat) := [(2902873088,101321810378058,101322191501556),(2902964224,101322217815428,101322598939155)]
theorem point_links_checked22117 : (cuts22117.take 2).map (fun c => (2902851585-1+2*2^9*c.k,101321716225429+c.lower,101322097348874+c.upper)) = pointBounds22117 := by
 decide +kernel
def cuts22118 : List PrefixCut := [⟨71,325686500,325686691⟩,
⟨128,581847376,581847714⟩]
theorem checked22118 : checkPrefixCuts (2^48) 2902982657 9 Manual.Count131072.C022118.packed 128 cuts22118 = true := by
 decide +kernel
def pointBounds22118 : List (Nat × Nat × Nat) := [(2903055360,101322623979472,101323005103434)]
theorem point_links_checked22118 : (cuts22118.take 1).map (fun c => (2902982657-1+2*2^9*c.k,101322298292972+c.lower,101322679416743+c.upper)) = pointBounds22118 := by
 decide +kernel
def cuts22119 : List PrefixCut := [⟨32,141749181,141749259⟩,
⟨121,543524821,543525131⟩,
⟨128,576973245,576973573⟩]
theorem checked22119 : checkPrefixCuts (2^48) 2903113729 9 Manual.Count131072.C022119.packed 128 cuts22119 = true := by
 decide +kernel
def pointBounds22119 : List (Nat × Nat × Nat) := [(2903146496,101323021889529,101323403013716),(2903237632,101323423665169,101323804789588)]
theorem point_links_checked22119 : (cuts22119.take 2).map (fun c => (2903113729-1+2*2^9*c.k,101322880140348+c.lower,101323261264457+c.upper)) = pointBounds22119 := by
 decide +kernel
def cuts22120 : List PrefixCut := [⟨82,378688364,378688586⟩,
⟨128,587805727,587806070⟩]
theorem checked22120 : checkPrefixCuts (2^48) 2903244801 9 Manual.Count131072.C022120.packed 128 cuts22120 = true := by
 decide +kernel
def pointBounds22120 : List (Nat × Nat × Nat) := [(2903328768,101323835801957,101324216926616)]
theorem point_links_checked22120 : (cuts22120.take 1).map (fun c => (2903244801-1+2*2^9*c.k,101323457113593+c.lower,101323838238030+c.upper)) = pointBounds22120 := by
 decide +kernel
def cuts22121 : List PrefixCut := [⟨43,191954483,191954600⟩,
⟨128,581768442,581768779⟩]
theorem checked22121 : checkPrefixCuts (2^48) 2903375873 9 Manual.Count131072.C022121.packed 128 cuts22121 = true := by
 decide +kernel
def pointBounds22121 : List (Nat × Nat × Nat) := [(2903419904,101324236873803,101324617998700)]
theorem point_links_checked22121 : (cuts22121.take 1).map (fun c => (2903375873-1+2*2^9*c.k,101324044919320+c.lower,101324426044100+c.upper)) = pointBounds22121 := by
 decide +kernel
def cuts22122 : List PrefixCut := [⟨4,19194716,19194726⟩,
⟨93,426639519,426639761⟩,
⟨128,586104657,586104988⟩]
theorem checked22122 : checkPrefixCuts (2^48) 2903506945 9 Manual.Count131072.C022122.packed 128 cuts22122 = true := by
 decide +kernel
def pointBounds22122 : List (Nat × Nat × Nat) := [(2903511040,101324645882478,101325027007605),(2903602176,101325053327281,101325434452640)]
theorem point_links_checked22122 : (cuts22122.take 2).map (fun c => (2903506945-1+2*2^9*c.k,101324626687762+c.lower,101325007812879+c.upper)) = pointBounds22122 := by
 decide +kernel
def cuts22123 : List PrefixCut := [⟨54,244283183,244283323⟩,
⟨128,581425194,581425516⟩]
theorem checked22123 : checkPrefixCuts (2^48) 2903638017 9 Manual.Count131072.C022123.packed 128 cuts22123 = true := by
 decide +kernel
def pointBounds22123 : List (Nat × Nat × Nat) := [(2903693312,101325457075602,101325838201190)]
theorem point_links_checked22123 : (cuts22123.take 1).map (fun c => (2903638017-1+2*2^9*c.k,101325212792419+c.lower,101325593917867+c.upper)) = pointBounds22123 := by
 decide +kernel
def cuts22124 : List PrefixCut := [⟨15,67272244,67272284⟩,
⟨104,472158428,472158696⟩,
⟨128,583628340,583628672⟩]
theorem checked22124 : checkPrefixCuts (2^48) 2903769089 9 Manual.Count131072.C022124.packed 128 cuts22124 = true := by
 decide +kernel
def pointBounds22124 : List (Nat × Nat × Nat) := [(2903784448,101325861489857,101326242615667),(2903875584,101326266376041,101326647502079)]
theorem point_links_checked22124 : (cuts22124.take 2).map (fun c => (2903769089-1+2*2^9*c.k,101325794217613+c.lower,101326175343383+c.upper)) = pointBounds22124 := by
 decide +kernel
def cuts22125 : List PrefixCut := [⟨65,298250013,298250174⟩,
⟨128,583311290,583311614⟩]
theorem checked22125 : checkPrefixCuts (2^48) 2903900161 9 Manual.Count131072.C022125.packed 128 cuts22125 = true := by
 decide +kernel
def pointBounds22125 : List (Nat × Nat × Nat) := [(2903966720,101326676095966,101327057222229)]
theorem point_links_checked22125 : (cuts22125.take 1).map (fun c => (2903900161-1+2*2^9*c.k,101326377845953+c.lower,101326758972055+c.upper)) = pointBounds22125 := by
 decide +kernel
def cuts22126 : List PrefixCut := [⟨26,115437825,115437889⟩,
⟨115,518056645,518056940⟩,
⟨128,581830941,581831272⟩]
theorem checked22126 : checkPrefixCuts (2^48) 2904031233 9 Manual.Count131072.C022126.packed 128 cuts22126 = true := by
 decide +kernel
def pointBounds22126 : List (Nat × Nat × Nat) := [(2904057856,101327076595068,101327457721558),(2904148992,101327479213888,101327860340609)]
theorem point_links_checked22126 : (cuts22126.take 2).map (fun c => (2904031233-1+2*2^9*c.k,101326961157243+c.lower,101327342283669+c.upper)) = pointBounds22126 := by
 decide +kernel
def cuts22127 : List PrefixCut := [⟨76,345616361,345616558⟩,
⟨128,585100041,585100370⟩]
theorem checked22127 : checkPrefixCuts (2^48) 2904162305 9 Manual.Count131072.C022127.packed 128 cuts22127 = true := by
 decide +kernel
def pointBounds22127 : List (Nat × Nat × Nat) := [(2904240128,101327888604545,101328269731499)]
theorem point_links_checked22127 : (cuts22127.take 1).map (fun c => (2904162305-1+2*2^9*c.k,101327542988184+c.lower,101327924114941+c.upper)) = pointBounds22127 := by
 decide +kernel
def cuts22128 : List PrefixCut := [⟨37,168828012,168828114⟩,
⟨126,575188590,575188925⟩,
⟨128,584104539,584104879⟩]
theorem checked22128 : checkPrefixCuts (2^48) 2904293377 9 Manual.Count131072.C022128.packed 128 cuts22128 = true := by
 decide +kernel
def pointBounds22128 : List (Nat × Nat × Nat) := [(2904331264,101328296916237,101328678043425),(2904422400,101328703276815,101329084404236)]
theorem point_links_checked22128 : (cuts22128.take 2).map (fun c => (2904293377-1+2*2^9*c.k,101328128088225+c.lower,101328509215311+c.upper)) = pointBounds22128 := by
 decide +kernel
def cuts22129 : List PrefixCut := [⟨87,395396737,395396958⟩,
⟨128,582721391,582721719⟩]
theorem checked22129 : checkPrefixCuts (2^48) 2904424449 9 Manual.Count131072.C022129.packed 128 cuts22129 = true := by
 decide +kernel
def pointBounds22129 : List (Nat × Nat × Nat) := [(2904513536,101329107589501,101329488717148)]
theorem point_links_checked22129 : (cuts22129.take 1).map (fun c => (2904424449-1+2*2^9*c.k,101328712192764+c.lower,101329093320190+c.upper)) = pointBounds22129 := by
 decide +kernel
def cuts22130 : List PrefixCut := [⟨48,219010402,219010524⟩,
⟨128,587540391,587540722⟩]
theorem checked22130 : checkPrefixCuts (2^48) 2904555521 9 Manual.Count131072.C022130.packed 128 cuts22130 = true := by
 decide +kernel
def pointBounds22130 : List (Nat × Nat × Nat) := [(2904604672,101329513924557,101329895052433)]
theorem point_links_checked22130 : (cuts22130.take 1).map (fun c => (2904555521-1+2*2^9*c.k,101329294914155+c.lower,101329676041909+c.upper)) = pointBounds22130 := by
 decide +kernel
def cuts22131 : List PrefixCut := [⟨9,43509696,43509721⟩,
⟨98,444683477,444683730⟩,
⟨128,584800667,584801000⟩]
theorem checked22131 : checkPrefixCuts (2^48) 2904686593 9 Manual.Count131072.C022131.packed 128 cuts22131 = true := by
 decide +kernel
def pointBounds22131 : List (Nat × Nat × Nat) := [(2904695808,101329925964242,101330307092352),(2904786944,101330327138023,101330708266361)]
theorem point_links_checked22131 : (cuts22131.take 2).map (fun c => (2904686593-1+2*2^9*c.k,101329882454546+c.lower,101330263582631+c.upper)) = pointBounds22131 := by
 decide +kernel
def cuts22132 : List PrefixCut := [⟨59,263854158,263854310⟩,
⟨128,571983910,571984239⟩]
theorem checked22132 : checkPrefixCuts (2^48) 2904817665 9 Manual.Count131072.C022132.packed 128 cuts22132 = true := by
 decide +kernel
def pointBounds22132 : List (Nat × Nat × Nat) := [(2904878080,101330731109371,101331112237941)]
theorem point_links_checked22132 : (cuts22132.take 1).map (fun c => (2904817665-1+2*2^9*c.k,101330467255213+c.lower,101330848383631+c.upper)) = pointBounds22132 := by
 decide +kernel
def cuts22133 : List PrefixCut := [⟨20,92437460,92437510⟩,
⟨109,501324899,501325187⟩,
⟨128,589883193,589883532⟩]
theorem checked22133 : checkPrefixCuts (2^48) 2904948737 9 Manual.Count131072.C022133.packed 128 cuts22133 = true := by
 decide +kernel
def pointBounds22133 : List (Nat × Nat × Nat) := [(2904969216,101331131676583,101331512805380),(2905060352,101331540564022,101331921693057)]
theorem point_links_checked22133 : (cuts22133.take 2).map (fun c => (2904948737-1+2*2^9*c.k,101331039239123+c.lower,101331420367870+c.upper)) = pointBounds22133 := by
 decide +kernel
def cuts22134 : List PrefixCut := [⟨70,325451469,325451656⟩,
⟨128,588790876,588791214⟩]
theorem checked22134 : checkPrefixCuts (2^48) 2905079809 9 Manual.Count131072.C022134.packed 128 cuts22134 = true := by
 decide +kernel
def pointBounds22134 : List (Nat × Nat × Nat) := [(2905151488,101331954573785,101332335703058)]
theorem point_links_checked22134 : (cuts22134.take 1).map (fun c => (2905079809-1+2*2^9*c.k,101331629122316+c.lower,101332010251402+c.upper)) = pointBounds22134 := by
 decide +kernel
def cuts22135 : List PrefixCut := [⟨31,144747230,144747315⟩,
⟨120,548073820,548074140⟩,
⟨128,586632849,586633191⟩]
theorem checked22135 : checkPrefixCuts (2^48) 2905210881 9 Manual.Count131072.C022135.packed 128 cuts22135 = true := by
 decide +kernel
def pointBounds22135 : List (Nat × Nat × Nat) := [(2905242624,101332362660422,101332743789931),(2905333760,101332765987012,101333147116756)]
theorem point_links_checked22135 : (cuts22135.take 2).map (fun c => (2905210881-1+2*2^9*c.k,101332217913192+c.lower,101332599042616+c.upper)) = pointBounds22135 := by
 decide +kernel
def cuts22136 : List PrefixCut := [⟨81,363979920,363980128⟩,
⟨128,578759067,578759399⟩]
theorem checked22136 : checkPrefixCuts (2^48) 2905341953 9 Manual.Count131072.C022136.packed 128 cuts22136 = true := by
 decide +kernel
def pointBounds22136 : List (Nat × Nat × Nat) := [(2905424896,101333168525961,101333549655935)]
theorem point_links_checked22136 : (cuts22136.take 1).map (fun c => (2905341953-1+2*2^9*c.k,101332804546041+c.lower,101333185675807+c.upper)) = pointBounds22136 := by
 decide +kernel
def cuts22137 : List PrefixCut := [⟨42,191815993,191816101⟩,
⟨128,583964257,583964585⟩]
theorem checked22137 : checkPrefixCuts (2^48) 2905473025 9 Manual.Count131072.C022137.packed 128 cuts22137 = true := by
 decide +kernel
def pointBounds22137 : List (Nat × Nat × Nat) := [(2905516032,101333575121101,101333956251307)]
theorem point_links_checked22137 : (cuts22137.take 1).map (fun c => (2905473025-1+2*2^9*c.k,101333383305108+c.lower,101333764435206+c.upper)) = pointBounds22137 := by
 decide +kernel
def cuts22138 : List PrefixCut := [⟨3,13949720,13949728⟩,
⟨92,417710051,417710290⟩,
⟨128,579481854,579482184⟩]
theorem checked22138 : checkPrefixCuts (2^48) 2905604097 9 Manual.Count131072.C022138.packed 128 cuts22138 = true := by
 decide +kernel
def pointBounds22138 : List (Nat × Nat × Nat) := [(2905607168,101333981219085,101334362349519),(2905698304,101334384979416,101334766110081)]
theorem point_links_checked22138 : (cuts22138.take 2).map (fun c => (2905604097-1+2*2^9*c.k,101333967269365+c.lower,101334348399791+c.upper)) = pointBounds22138 := by
 decide +kernel
def cuts22139 : List PrefixCut := [⟨53,236357526,236357658⟩,
⟨128,577518350,577518682⟩]
theorem checked22139 : checkPrefixCuts (2^48) 2905735169 9 Manual.Count131072.C022139.packed 128 cuts22139 = true := by
 decide +kernel
def pointBounds22139 : List (Nat × Nat × Nat) := [(2905789440,101334783108745,101335164239633)]
theorem point_links_checked22139 : (cuts22139.take 1).map (fun c => (2905735169-1+2*2^9*c.k,101334546751219+c.lower,101334927881975+c.upper)) = pointBounds22139 := by
 decide +kernel
def cuts22140 : List PrefixCut := [⟨14,62186772,62186806⟩,
⟨103,469008754,469009013⟩,
⟨128,585628699,585629024⟩]
theorem checked22140 : checkPrefixCuts (2^48) 2905866241 9 Manual.Count131072.C022140.packed 128 cuts22140 = true := by
 decide +kernel
def pointBounds22140 : List (Nat × Nat × Nat) := [(2905880576,101335186456341,101335567587463),(2905971712,101335593278323,101335974409670)]
theorem point_links_checked22140 : (cuts22140.take 2).map (fun c => (2905866241-1+2*2^9*c.k,101335124269569+c.lower,101335505400657+c.upper)) = pointBounds22140 := by
 decide +kernel
def cuts22141 : List PrefixCut := [⟨64,290383019,290383186⟩,
⟨128,576691468,576691798⟩]
theorem checked22141 : checkPrefixCuts (2^48) 2905997313 9 Manual.Count131072.C022141.packed 128 cuts22141 = true := by
 decide +kernel
def pointBounds22141 : List (Nat × Nat × Nat) := [(2906062848,101336000281287,101336381412867)]
theorem point_links_checked22141 : (cuts22141.take 1).map (fun c => (2905997313-1+2*2^9*c.k,101335709898268+c.lower,101336091029681+c.upper)) = pointBounds22141 := by
 decide +kernel
def cuts22142 : List PrefixCut := [⟨25,114676565,114676628⟩,
⟨114,521072858,521073155⟩,
⟨128,587319278,587319615⟩]
theorem checked22142 : checkPrefixCuts (2^48) 2906128385 9 Manual.Count131072.C022142.packed 128 cuts22142 = true := by
 decide +kernel
def pointBounds22142 : List (Nat × Nat × Nat) := [(2906153984,101336401266301,101336782398107),(2906245120,101336807662594,101337188794634)]
theorem point_links_checked22142 : (cuts22142.take 2).map (fun c => (2906128385-1+2*2^9*c.k,101336286589736+c.lower,101336667721479+c.upper)) = pointBounds22142 := by
 decide +kernel
def cuts22143 : List PrefixCut := [⟨75,333841890,333842090⟩,
⟨128,578382609,578382946⟩]
theorem checked22143 : checkPrefixCuts (2^48) 2906259457 9 Manual.Count131072.C022143.packed 128 cuts22143 = true := by
 decide +kernel
def pointBounds22143 : List (Nat × Nat × Nat) := [(2906336256,101337207750904,101337588883184)]
theorem point_links_checked22143 : (cuts22143.take 1).map (fun c => (2906259457-1+2*2^9*c.k,101336873909014+c.lower,101337255041094+c.upper)) = pointBounds22143 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000066
