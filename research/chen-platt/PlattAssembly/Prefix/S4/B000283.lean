import PlattAssemblyKernel
import PlattCertificates.Count131072.C039056
import PlattCertificates.Count131072.C039057
import PlattCertificates.Count131072.C039058
import PlattCertificates.Count131072.C039059
import PlattCertificates.Count131072.C039060
import PlattCertificates.Count131072.C039061
import PlattCertificates.Count131072.C039062
import PlattCertificates.Count131072.C039063
import PlattCertificates.Count131072.C039064
import PlattCertificates.Count131072.C039065
import PlattCertificates.Count131072.C039066
import PlattCertificates.Count131072.C039067
import PlattCertificates.Count131072.C039068
import PlattCertificates.Count131072.C039069
import PlattCertificates.Count131072.C039070
import PlattCertificates.Count131072.C039071
import PlattCertificates.Count131072.C039072
import PlattCertificates.Count131072.C039073
import PlattCertificates.Count131072.C039074
import PlattCertificates.Count131072.C039075
import PlattCertificates.Count131072.C039076
import PlattCertificates.Count131072.C039077
import PlattCertificates.Count131072.C039078
import PlattCertificates.Count131072.C039079
import PlattCertificates.Count131072.C039080
import PlattCertificates.Count131072.C039081
import PlattCertificates.Count131072.C039082
import PlattCertificates.Count131072.C039083
import PlattCertificates.Count131072.C039084
import PlattCertificates.Count131072.C039085
import PlattCertificates.Count131072.C039086
import PlattCertificates.Count131072.C039087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000283
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts39056 : List PrefixCut := [⟨36,180539790,180539901⟩,
⟨64,319706394,319706590⟩]
theorem checked39056 : checkPrefixCuts (2^48) 5123080193 10 Manual.Count131072.C039056.packed 64 cuts39056 = true := by
 decide +kernel
def pointBounds39056 : List (Nat × Nat × Nat) := [(5123153920,108566092150753,108566477477524)]
theorem point_links_checked39056 : (cuts39056.take 1).map (fun c => (5123080193-1+2*2^10*c.k,108565911610963+c.lower,108566296937623+c.upper)) = pointBounds39056 := by
 decide +kernel
def cuts39057 : List PrefixCut := [⟨51,255308748,255308899⟩,
⟨64,319313670,319313861⟩]
theorem checked39057 : checkPrefixCuts (2^48) 5123211265 10 Manual.Count131072.C039057.packed 64 cuts39057 = true := by
 decide +kernel
def pointBounds39057 : List (Nat × Nat × Nat) := [(5123315712,108566486626105,108566871953112)]
theorem point_links_checked39057 : (cuts39057.take 1).map (fun c => (5123211265-1+2*2^10*c.k,108566231317357+c.lower,108566616644213+c.upper)) = pointBounds39057 := by
 decide +kernel
def cuts39058 : List PrefixCut := [⟨64,324085165,324085360⟩]
theorem checked39058 : checkPrefixCuts (2^48) 5123342337 10 Manual.Count131072.C039058.packed 64 cuts39058 = true := by
 decide +kernel
def cuts39059 : List PrefixCut := [⟨2,10218519,10218525⟩,
⟨64,325120693,325120887⟩]
theorem checked39059 : checkPrefixCuts (2^48) 5123473409 10 Manual.Count131072.C039059.packed 64 cuts39059 = true := by
 decide +kernel
def pointBounds39059 : List (Nat × Nat × Nat) := [(5123477504,108566884934711,108567270261959)]
theorem point_links_checked39059 : (cuts39059.take 1).map (fun c => (5123473409-1+2*2^10*c.k,108566874716192+c.lower,108567260043434+c.upper)) = pointBounds39059 := by
 decide +kernel
def cuts39060 : List PrefixCut := [⟨17,87294419,87294472⟩,
⟨64,319234205,319234399⟩]
theorem checked39060 : checkPrefixCuts (2^48) 5123604481 10 Manual.Count131072.C039060.packed 64 cuts39060 = true := by
 decide +kernel
def pointBounds39060 : List (Nat × Nat × Nat) := [(5123639296,108567287131304,108567672458793)]
theorem point_links_checked39060 : (cuts39060.take 1).map (fun c => (5123604481-1+2*2^10*c.k,108567199836885+c.lower,108567585164321+c.upper)) = pointBounds39060 := by
 decide +kernel
def cuts39061 : List PrefixCut := [⟨32,163706695,163706791⟩,
⟨64,325378735,325378928⟩]
theorem checked39061 : checkPrefixCuts (2^48) 5123735553 10 Manual.Count131072.C039061.packed 64 cuts39061 = true := by
 decide +kernel
def pointBounds39061 : List (Nat × Nat × Nat) := [(5123801088,108567682777785,108568068105511)]
theorem point_links_checked39061 : (cuts39061.take 1).map (fun c => (5123735553-1+2*2^10*c.k,108567519071090+c.lower,108567904398720+c.upper)) = pointBounds39061 := by
 decide +kernel
def cuts39062 : List PrefixCut := [⟨47,233907111,233907252⟩,
⟨64,320041833,320042025⟩]
theorem checked39062 : checkPrefixCuts (2^48) 5123866625 10 Manual.Count131072.C039062.packed 64 cuts39062 = true := by
 decide +kernel
def pointBounds39062 : List (Nat × Nat × Nat) := [(5123962880,108568078356936,108568463684900)]
theorem point_links_checked39062 : (cuts39062.take 1).map (fun c => (5123866625-1+2*2^10*c.k,108567844449825+c.lower,108568229777648+c.upper)) = pointBounds39062 := by
 decide +kernel
def cuts39063 : List PrefixCut := [⟨62,314430736,314430922⟩,
⟨64,324208505,324208697⟩]
theorem checked39063 : checkPrefixCuts (2^48) 5123997697 10 Manual.Count131072.C039063.packed 64 cuts39063 = true := by
 decide +kernel
def pointBounds39063 : List (Nat × Nat × Nat) := [(5124124672,108568478922394,108568864250595)]
theorem point_links_checked39063 : (cuts39063.take 1).map (fun c => (5123997697-1+2*2^10*c.k,108568164491658+c.lower,108568549819673+c.upper)) = pointBounds39063 := by
 decide +kernel
def cuts39064 : List PrefixCut := [⟨64,320135305,320135499⟩]
theorem checked39064 : checkPrefixCuts (2^48) 5124128769 10 Manual.Count131072.C039064.packed 64 cuts39064 = true := by
 decide +kernel
def cuts39065 : List PrefixCut := [⟨13,66190316,66190355⟩,
⟨64,326444014,326444205⟩]
theorem checked39065 : checkPrefixCuts (2^48) 5124259841 10 Manual.Count131072.C039065.packed 64 cuts39065 = true := by
 decide +kernel
def pointBounds39065 : List (Nat × Nat × Nat) := [(5124286464,108568875025784,108569260354224)]
theorem point_links_checked39065 : (cuts39065.take 1).map (fun c => (5124259841-1+2*2^10*c.k,108568808835468+c.lower,108569194163869+c.upper)) = pointBounds39065 := by
 decide +kernel
def cuts39066 : List PrefixCut := [⟨28,139297794,139297878⟩,
⟨64,323194903,323195096⟩]
theorem checked39066 : checkPrefixCuts (2^48) 5124390913 10 Manual.Count131072.C039066.packed 64 cuts39066 = true := by
 decide +kernel
def pointBounds39066 : List (Nat × Nat × Nat) := [(5124448256,108569274577276,108569659905952)]
theorem point_links_checked39066 : (cuts39066.take 1).map (fun c => (5124390913-1+2*2^10*c.k,108569135279482+c.lower,108569520608074+c.upper)) = pointBounds39066 := by
 decide +kernel
def cuts39067 : List PrefixCut := [⟨43,216191044,216191172⟩,
⟨64,320714993,320715186⟩]
theorem checked39067 : checkPrefixCuts (2^48) 5124521985 10 Manual.Count131072.C039067.packed 64 cuts39067 = true := by
 decide +kernel
def pointBounds39067 : List (Nat × Nat × Nat) := [(5124610048,108569674665429,108570059994342)]
theorem point_links_checked39067 : (cuts39067.take 1).map (fun c => (5124521985-1+2*2^10*c.k,108569458474385+c.lower,108569843803170+c.upper)) = pointBounds39067 := by
 decide +kernel
def cuts39068 : List PrefixCut := [⟨58,297034459,297034638⟩,
⟨64,328451163,328451361⟩]
theorem checked39068 : checkPrefixCuts (2^48) 5124653057 10 Manual.Count131072.C039068.packed 64 cuts39068 = true := by
 decide +kernel
def pointBounds39068 : List (Nat × Nat × Nat) := [(5124771840,108570076223837,108570461552994)]
theorem point_links_checked39068 : (cuts39068.take 1).map (fun c => (5124653057-1+2*2^10*c.k,108569779189378+c.lower,108570164518356+c.upper)) = pointBounds39068 := by
 decide +kernel
def cuts39069 : List PrefixCut := [⟨64,320369011,320369200⟩]
theorem checked39069 : checkPrefixCuts (2^48) 5124784129 10 Manual.Count131072.C039069.packed 64 cuts39069 = true := by
 decide +kernel
def cuts39070 : List PrefixCut := [⟨9,45311261,45311291⟩,
⟨64,320196073,320196268⟩]
theorem checked39070 : checkPrefixCuts (2^48) 5124915201 10 Manual.Count131072.C039070.packed 64 cuts39070 = true := by
 decide +kernel
def pointBounds39070 : List (Nat × Nat × Nat) := [(5124933632,108570473320813,108570858650208)]
theorem point_links_checked39070 : (cuts39070.take 1).map (fun c => (5124915201-1+2*2^10*c.k,108570428009552+c.lower,108570813338917+c.upper)) = pointBounds39070 := by
 decide +kernel
def cuts39071 : List PrefixCut := [⟨24,119783074,119783145⟩,
⟨64,324142151,324142343⟩]
theorem checked39071 : checkPrefixCuts (2^48) 5125046273 10 Manual.Count131072.C039071.packed 64 cuts39071 = true := by
 decide +kernel
def pointBounds39071 : List (Nat × Nat × Nat) := [(5125095424,108570867988699,108571253318330)]
theorem point_links_checked39071 : (cuts39071.take 1).map (fun c => (5125046273-1+2*2^10*c.k,108570748205625+c.lower,108571133535185+c.upper)) = pointBounds39071 := by
 decide +kernel
def cuts39072 : List PrefixCut := [⟨39,192767825,192767936⟩,
⟨64,318532107,318532293⟩]
theorem checked39072 : checkPrefixCuts (2^48) 5125177345 10 Manual.Count131072.C039072.packed 64 cuts39072 = true := by
 decide +kernel
def pointBounds39072 : List (Nat × Nat × Nat) := [(5125257216,108571265115601,108571650445464)]
theorem point_links_checked39072 : (cuts39072.take 1).map (fun c => (5125177345-1+2*2^10*c.k,108571072347776+c.lower,108571457677528+c.upper)) = pointBounds39072 := by
 decide +kernel
def cuts39073 : List PrefixCut := [⟨54,273986045,273986212⟩,
⟨64,325168998,325169194⟩]
theorem checked39073 : checkPrefixCuts (2^48) 5125308417 10 Manual.Count131072.C039073.packed 64 cuts39073 = true := by
 decide +kernel
def pointBounds39073 : List (Nat × Nat × Nat) := [(5125419008,108571664865928,108572050196033)]
theorem point_links_checked39073 : (cuts39073.take 1).map (fun c => (5125308417-1+2*2^10*c.k,108571390879883+c.lower,108571776209821+c.upper)) = pointBounds39073 := by
 decide +kernel
def cuts39074 : List PrefixCut := [⟨64,322359980,322360172⟩]
theorem checked39074 : checkPrefixCuts (2^48) 5125439489 10 Manual.Count131072.C039074.packed 64 cuts39074 = true := by
 decide +kernel
def cuts39075 : List PrefixCut := [⟨5,25096502,25096518⟩,
⟨64,318507666,318507858⟩]
theorem checked39075 : checkPrefixCuts (2^48) 5125570561 10 Manual.Count131072.C039075.packed 64 cuts39075 = true := by
 decide +kernel
def pointBounds39075 : List (Nat × Nat × Nat) := [(5125580800,108572063505363,108572448835705)]
theorem point_links_checked39075 : (cuts39075.take 1).map (fun c => (5125570561-1+2*2^10*c.k,108572038408861+c.lower,108572423739187+c.upper)) = pointBounds39075 := by
 decide +kernel
def cuts39076 : List PrefixCut := [⟨20,101426520,101426579⟩,
⟨64,324430202,324430393⟩]
theorem checked39076 : checkPrefixCuts (2^48) 5125701633 10 Manual.Count131072.C039076.packed 64 cuts39076 = true := by
 decide +kernel
def pointBounds39076 : List (Nat × Nat × Nat) := [(5125742592,108572458343047,108572843673624)]
theorem point_links_checked39076 : (cuts39076.take 1).map (fun c => (5125701633-1+2*2^10*c.k,108572356916527+c.lower,108572742247045+c.upper)) = pointBounds39076 := by
 decide +kernel
def cuts39077 : List PrefixCut := [⟨35,177148120,177148224⟩,
⟨64,326618371,326618562⟩]
theorem checked39077 : checkPrefixCuts (2^48) 5125832705 10 Manual.Count131072.C039077.packed 64 cuts39077 = true := by
 decide +kernel
def pointBounds39077 : List (Nat × Nat × Nat) := [(5125904384,108572858494849,108573243825662)]
theorem point_links_checked39077 : (cuts39077.take 1).map (fun c => (5125832705-1+2*2^10*c.k,108572681346729+c.lower,108573066677438+c.upper)) = pointBounds39077 := by
 decide +kernel
def cuts39078 : List PrefixCut := [⟨50,250449336,250449485⟩,
⟨64,319526559,319526750⟩]
theorem checked39078 : checkPrefixCuts (2^48) 5125963777 10 Manual.Count131072.C039078.packed 64 cuts39078 = true := by
 decide +kernel
def pointBounds39078 : List (Nat × Nat × Nat) := [(5126066176,108573258414436,108573643745485)]
theorem point_links_checked39078 : (cuts39078.take 1).map (fun c => (5125963777-1+2*2^10*c.k,108573007965100+c.lower,108573393296000+c.upper)) = pointBounds39078 := by
 decide +kernel
def cuts39079 : List PrefixCut := [⟨64,321385311,321385498⟩]
theorem checked39079 : checkPrefixCuts (2^48) 5126094849 10 Manual.Count131072.C039079.packed 64 cuts39079 = true := by
 decide +kernel
def cuts39080 : List PrefixCut := [⟨1,4886882,4886885⟩,
⟨64,322639976,322640167⟩]
theorem checked39080 : checkPrefixCuts (2^48) 5126225921 10 Manual.Count131072.C039080.packed 64 cuts39080 = true := by
 decide +kernel
def pointBounds39080 : List (Nat × Nat × Nat) := [(5126227968,108573653763852,108574039095133)]
theorem point_links_checked39080 : (cuts39080.take 1).map (fun c => (5126225921-1+2*2^10*c.k,108573648876970+c.lower,108574034208248+c.upper)) = pointBounds39080 := by
 decide +kernel
def cuts39081 : List PrefixCut := [⟨16,79340923,79340971⟩,
⟨64,323125839,323126031⟩]
theorem checked39081 : checkPrefixCuts (2^48) 5126356993 10 Manual.Count131072.C039081.packed 64 cuts39081 = true := by
 decide +kernel
def pointBounds39081 : List (Nat × Nat × Nat) := [(5126389760,108574050857869,108574436189386)]
theorem point_links_checked39081 : (cuts39081.take 1).map (fun c => (5126356993-1+2*2^10*c.k,108573971516946+c.lower,108574356848415+c.upper)) = pointBounds39081 := by
 decide +kernel
def cuts39082 : List PrefixCut := [⟨31,157359594,157359686⟩,
⟨64,323941206,323941398⟩]
theorem checked39082 : checkPrefixCuts (2^48) 5126488065 10 Manual.Count131072.C039082.packed 64 cuts39082 = true := by
 decide +kernel
def pointBounds39082 : List (Nat × Nat × Nat) := [(5126551552,108574452002379,108574837334132)]
theorem point_links_checked39082 : (cuts39082.take 1).map (fun c => (5126488065-1+2*2^10*c.k,108574294642785+c.lower,108574679974446+c.upper)) = pointBounds39082 := by
 decide +kernel
def cuts39083 : List PrefixCut := [⟨46,230157893,230158028⟩,
⟨64,320419046,320419235⟩]
theorem checked39083 : checkPrefixCuts (2^48) 5126619137 10 Manual.Count131072.C039083.packed 64 cuts39083 = true := by
 decide +kernel
def pointBounds39083 : List (Nat × Nat × Nat) := [(5126713344,108574848741884,108575234073872)]
theorem point_links_checked39083 : (cuts39083.take 1).map (fun c => (5126619137-1+2*2^10*c.k,108574618583991+c.lower,108575003915844+c.upper)) = pointBounds39083 := by
 decide +kernel
def cuts39084 : List PrefixCut := [⟨61,306410899,306411081⟩,
⟨64,321893210,321893401⟩]
theorem checked39084 : checkPrefixCuts (2^48) 5126750209 10 Manual.Count131072.C039084.packed 64 cuts39084 = true := by
 decide +kernel
def pointBounds39084 : List (Nat × Nat × Nat) := [(5126875136,108575245413936,108575630746160)]
theorem point_links_checked39084 : (cuts39084.take 1).map (fun c => (5126750209-1+2*2^10*c.k,108574939003037+c.lower,108575324335079+c.upper)) = pointBounds39084 := by
 decide +kernel
def cuts39085 : List PrefixCut := [⟨64,321335971,321336163⟩]
theorem checked39085 : checkPrefixCuts (2^48) 5126881281 10 Manual.Count131072.C039085.packed 64 cuts39085 = true := by
 decide +kernel
def cuts39086 : List PrefixCut := [⟨12,60390266,60390300⟩,
⟨64,322151277,322151465⟩]
theorem checked39086 : checkPrefixCuts (2^48) 5127012353 10 Manual.Count131072.C039086.packed 64 cuts39086 = true := by
 decide +kernel
def pointBounds39086 : List (Nat × Nat × Nat) := [(5127036928,108575642622484,108576027954943)]
theorem point_links_checked39086 : (cuts39086.take 1).map (fun c => (5127012353-1+2*2^10*c.k,108575582232218+c.lower,108575967564643+c.upper)) = pointBounds39086 := by
 decide +kernel
def cuts39087 : List PrefixCut := [⟨27,136862382,136862464⟩,
⟨64,323954671,323954869⟩]
theorem checked39087 : checkPrefixCuts (2^48) 5127143425 10 Manual.Count131072.C039087.packed 64 cuts39087 = true := by
 decide +kernel
def pointBounds39087 : List (Nat × Nat × Nat) := [(5127198720,108576041245877,108576426578572)]
theorem point_links_checked39087 : (cuts39087.take 1).map (fun c => (5127143425-1+2*2^10*c.k,108575904383495+c.lower,108576289716108+c.upper)) = pointBounds39087 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000283
