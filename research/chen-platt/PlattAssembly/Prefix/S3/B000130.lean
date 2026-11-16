import PlattAssemblyKernel
import PlattCertificates.Count131072.C024160
import PlattCertificates.Count131072.C024161
import PlattCertificates.Count131072.C024162
import PlattCertificates.Count131072.C024163
import PlattCertificates.Count131072.C024164
import PlattCertificates.Count131072.C024165
import PlattCertificates.Count131072.C024166
import PlattCertificates.Count131072.C024167
import PlattCertificates.Count131072.C024168
import PlattCertificates.Count131072.C024169
import PlattCertificates.Count131072.C024170
import PlattCertificates.Count131072.C024171
import PlattCertificates.Count131072.C024172
import PlattCertificates.Count131072.C024173
import PlattCertificates.Count131072.C024174
import PlattCertificates.Count131072.C024175
import PlattCertificates.Count131072.C024176
import PlattCertificates.Count131072.C024177
import PlattCertificates.Count131072.C024178
import PlattCertificates.Count131072.C024179
import PlattCertificates.Count131072.C024180
import PlattCertificates.Count131072.C024181
import PlattCertificates.Count131072.C024182
import PlattCertificates.Count131072.C024183
import PlattCertificates.Count131072.C024184
import PlattCertificates.Count131072.C024185
import PlattCertificates.Count131072.C024186
import PlattCertificates.Count131072.C024187
import PlattCertificates.Count131072.C024188
import PlattCertificates.Count131072.C024189
import PlattCertificates.Count131072.C024190
import PlattCertificates.Count131072.C024191
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts24160 : List PrefixCut := [⟨57,235342089,235342219⟩,
⟨128,530068450,530068740⟩]
theorem checked24160 : checkPrefixCuts (2^48) 3170631681 9 Manual.Count131072.C024160.packed 128 cuts24160 = true := by
 decide +kernel
def pointBounds24160 : List (Nat × Nat × Nat) := [(3170690048,102459457014797,102459838784356)]
theorem point_links_checked24160 : (cuts24160.take 1).map (fun c => (3170631681-1+2*2^9*c.k,102459221672708+c.lower,102459603442137+c.upper)) = pointBounds24160 := by
 decide +kernel
def cuts24161 : List PrefixCut := [⟨26,107324878,107324938⟩,
⟨123,511582786,511583080⟩,
⟨128,533064734,533065042⟩]
theorem checked24161 : checkPrefixCuts (2^48) 3170762753 9 Manual.Count131072.C024161.packed 128 cuts24161 = true := by
 decide +kernel
def pointBounds24161 : List (Nat × Nat × Nat) := [(3170789376,102459859066036,102460240835815),(3170888704,102460263323944,102460645093957)]
theorem point_links_checked24161 : (cuts24161.take 2).map (fun c => (3170762753-1+2*2^9*c.k,102459751741158+c.lower,102460133510877+c.upper)) = pointBounds24161 := by
 decide +kernel
def cuts24162 : List PrefixCut := [⟨92,384006055,384006271⟩,
⟨128,537747315,537747614⟩]
theorem checked24162 : checkPrefixCuts (2^48) 3170893825 9 Manual.Count131072.C024162.packed 128 cuts24162 = true := by
 decide +kernel
def pointBounds24162 : List (Nat × Nat × Nat) := [(3170988032,102460668811947,102461050582190)]
theorem point_links_checked24162 : (cuts24162.take 1).map (fun c => (3170893825-1+2*2^9*c.k,102460284805892+c.lower,102460666575919+c.upper)) = pointBounds24162 := by
 decide +kernel
def cuts24163 : List PrefixCut := [⟨61,252177861,252178005⟩,
⟨128,526896042,526896341⟩]
theorem checked24163 : checkPrefixCuts (2^48) 3171024897 9 Manual.Count131072.C024163.packed 128 cuts24163 = true := by
 decide +kernel
def pointBounds24163 : List (Nat × Nat × Nat) := [(3171087360,102461074731068,102461456501538)]
theorem point_links_checked24163 : (cuts24163.take 1).map (fun c => (3171024897-1+2*2^9*c.k,102460822553207+c.lower,102461204323533+c.upper)) = pointBounds24163 := by
 decide +kernel
def cuts24164 : List PrefixCut := [⟨30,122755840,122755910⟩,
⟨127,530868493,530868797⟩,
⟨128,534596300,534596607⟩]
theorem checked24164 : checkPrefixCuts (2^48) 3171155969 9 Manual.Count131072.C024164.packed 128 cuts24164 = true := by
 decide +kernel
def pointBounds24164 : List (Nat × Nat × Nat) := [(3171186688,102461472205089,102461853975784),(3171286016,102461880317742,102462262088671)]
theorem point_links_checked24164 : (cuts24164.take 2).map (fun c => (3171155969-1+2*2^9*c.k,102461349449249+c.lower,102461731219874+c.upper)) = pointBounds24164 := by
 decide +kernel
def cuts24165 : List PrefixCut := [⟨96,405259588,405259817⟩,
⟨128,537059421,537059724⟩]
theorem checked24165 : checkPrefixCuts (2^48) 3171287041 9 Manual.Count131072.C024165.packed 128 cuts24165 = true := by
 decide +kernel
def pointBounds24165 : List (Nat × Nat × Nat) := [(3171385344,102462289305137,102462671076298)]
theorem point_links_checked24165 : (cuts24165.take 1).map (fun c => (3171287041-1+2*2^9*c.k,102461884045549+c.lower,102462265816481+c.upper)) = pointBounds24165 := by
 decide +kernel
def cuts24166 : List PrefixCut := [⟨65,270340733,270340886⟩,
⟨128,525943226,525943520⟩]
theorem checked24166 : checkPrefixCuts (2^48) 3171418113 9 Manual.Count131072.C024166.packed 128 cuts24166 = true := by
 decide +kernel
def pointBounds24166 : List (Nat × Nat × Nat) := [(3171484672,102462691445703,102463073217091)]
theorem point_links_checked24166 : (cuts24166.take 1).map (fun c => (3171418113-1+2*2^9*c.k,102462421104970+c.lower,102462802876205+c.upper)) = pointBounds24166 := by
 decide +kernel
def cuts24167 : List PrefixCut := [⟨34,148477894,148477974⟩,
⟨128,525921630,525921925⟩]
theorem checked24167 : checkPrefixCuts (2^48) 3171549185 9 Manual.Count131072.C024167.packed 128 cuts24167 = true := by
 decide +kernel
def pointBounds24167 : List (Nat × Nat × Nat) := [(3171584000,102463095526090,102463477297699)]
theorem point_links_checked24167 : (cuts24167.take 1).map (fun c => (3171549185-1+2*2^9*c.k,102462947048196+c.lower,102463328819725+c.upper)) = pointBounds24167 := by
 decide +kernel
def cuts24168 : List PrefixCut := [⟨3,11359521,11359528⟩,
⟨100,421094392,421094626⟩,
⟨128,532910620,532910915⟩]
theorem checked24168 : checkPrefixCuts (2^48) 3171680257 9 Manual.Count131072.C024168.packed 128 cuts24168 = true := by
 decide +kernel
def pointBounds24168 : List (Nat × Nat × Nat) := [(3171683328,102463484329347,102463866101178),(3171782656,102463894064218,102464275836276)]
theorem point_links_checked24168 : (cuts24168.take 2).map (fun c => (3171680257-1+2*2^9*c.k,102463472969826+c.lower,102463854741650+c.upper)) = pointBounds24168 := by
 decide +kernel
def cuts24169 : List PrefixCut := [⟨69,294622264,294622428⟩,
⟨128,535373371,535373673⟩]
theorem checked24169 : checkPrefixCuts (2^48) 3171811329 9 Manual.Count131072.C024169.packed 128 cuts24169 = true := by
 decide +kernel
def pointBounds24169 : List (Nat × Nat × Nat) := [(3171881984,102464300502710,102464682274993)]
theorem point_links_checked24169 : (cuts24169.take 1).map (fun c => (3171811329-1+2*2^9*c.k,102464005880446+c.lower,102464387652565+c.upper)) = pointBounds24169 := by
 decide +kernel
def cuts24170 : List PrefixCut := [⟨38,157333239,157333328⟩,
⟨128,525412576,525412874⟩]
theorem checked24170 : checkPrefixCuts (2^48) 3171942401 9 Manual.Count131072.C024170.packed 128 cuts24170 = true := by
 decide +kernel
def pointBounds24170 : List (Nat × Nat × Nat) := [(3171981312,102464698587056,102465080359566)]
theorem point_links_checked24170 : (cuts24170.take 1).map (fun c => (3171942401-1+2*2^9*c.k,102464541253817+c.lower,102464923026238+c.upper)) = pointBounds24170 := by
 decide +kernel
def cuts24171 : List PrefixCut := [⟨7,30436175,30436190⟩,
⟨104,433997080,433997319⟩,
⟨128,534796611,534796905⟩]
theorem checked24171 : checkPrefixCuts (2^48) 3172073473 9 Manual.Count131072.C024171.packed 128 cuts24171 = true := by
 decide +kernel
def pointBounds24171 : List (Nat × Nat × Nat) := [(3172080640,102465097102568,102465478875302),(3172179968,102465500663473,102465882436431)]
theorem point_links_checked24171 : (cuts24171.take 2).map (fun c => (3172073473-1+2*2^9*c.k,102465066666393+c.lower,102465448439112+c.upper)) = pointBounds24171 := by
 decide +kernel
def cuts24172 : List PrefixCut := [⟨73,298578439,298578608⟩,
⟨128,531047792,531048087⟩]
theorem checked24172 : checkPrefixCuts (2^48) 3172204545 9 Manual.Count131072.C024172.packed 128 cuts24172 = true := by
 decide +kernel
def pointBounds24172 : List (Nat × Nat × Nat) := [(3172279296,102465900041443,102466281814625)]
theorem point_links_checked24172 : (cuts24172.take 1).map (fun c => (3172204545-1+2*2^9*c.k,102465601463004+c.lower,102465983236017+c.upper)) = pointBounds24172 := by
 decide +kernel
def cuts24173 : List PrefixCut := [⟨42,173018371,173018466⟩,
⟨128,530049931,530050231⟩]
theorem checked24173 : checkPrefixCuts (2^48) 3172335617 9 Manual.Count131072.C024173.packed 128 cuts24173 = true := by
 decide +kernel
def pointBounds24173 : List (Nat × Nat × Nat) := [(3172378624,102466305529167,102466687302570)]
theorem point_links_checked24173 : (cuts24173.take 1).map (fun c => (3172335617-1+2*2^9*c.k,102466132510796+c.lower,102466514284104+c.upper)) = pointBounds24173 := by
 decide +kernel
def cuts24174 : List PrefixCut := [⟨11,44983142,44983167⟩,
⟨108,446807808,446808065⟩,
⟨128,531181406,531181713⟩]
theorem checked24174 : checkPrefixCuts (2^48) 3172466689 9 Manual.Count131072.C024174.packed 128 cuts24174 = true := by
 decide +kernel
def pointBounds24174 : List (Nat × Nat × Nat) := [(3172477952,102466707543869,102467089317502),(3172577280,102467109368535,102467491142400)]
theorem point_links_checked24174 : (cuts24174.take 2).map (fun c => (3172466689-1+2*2^9*c.k,102466662560727+c.lower,102467044334335+c.upper)) = pointBounds24174 := by
 decide +kernel
def cuts24175 : List PrefixCut := [⟨77,316728729,316728909⟩,
⟨128,533466080,533466381⟩]
theorem checked24175 : checkPrefixCuts (2^48) 3172597761 9 Manual.Count131072.C024175.packed 128 cuts24175 = true := by
 decide +kernel
def pointBounds24175 : List (Nat × Nat × Nat) := [(3172676608,102467510470862,102467892244957)]
theorem point_links_checked24175 : (cuts24175.take 1).map (fun c => (3172597761-1+2*2^9*c.k,102467193742133+c.lower,102467575516048+c.upper)) = pointBounds24175 := by
 decide +kernel
def cuts24176 : List PrefixCut := [⟨46,197659949,197660062⟩,
⟨128,538234861,538235160⟩]
theorem checked24176 : checkPrefixCuts (2^48) 3172728833 9 Manual.Count131072.C024176.packed 128 cuts24176 = true := by
 decide +kernel
def pointBounds24176 : List (Nat × Nat × Nat) := [(3172775936,102467924868162,102468306642491)]
theorem point_links_checked24176 : (cuts24176.take 1).map (fun c => (3172728833-1+2*2^9*c.k,102467727208213+c.lower,102468108982429+c.upper)) = pointBounds24176 := by
 decide +kernel
def cuts24177 : List PrefixCut := [⟨15,66446108,66446146⟩,
⟨112,461478363,461478625⟩,
⟨128,525260763,525261061⟩]
theorem checked24177 : checkPrefixCuts (2^48) 3172859905 9 Manual.Count131072.C024177.packed 128 cuts24177 = true := by
 decide +kernel
def pointBounds24177 : List (Nat × Nat × Nat) := [(3172875264,102468331889182,102468713663735),(3172974592,102468726921437,102469108696214)]
theorem point_links_checked24177 : (cuts24177.take 2).map (fun c => (3172859905-1+2*2^9*c.k,102468265443074+c.lower,102468647217589+c.upper)) = pointBounds24177 := by
 decide +kernel
def cuts24178 : List PrefixCut := [⟨81,336559989,336560173⟩,
⟨128,531448509,531448800⟩]
theorem checked24178 : checkPrefixCuts (2^48) 3172990977 9 Manual.Count131072.C024178.packed 128 cuts24178 = true := by
 decide +kernel
def pointBounds24178 : List (Nat × Nat × Nat) := [(3173073920,102469127263826,102469509038823)]
theorem point_links_checked24178 : (cuts24178.take 1).map (fun c => (3172990977-1+2*2^9*c.k,102468790703837+c.lower,102469172478650+c.upper)) = pointBounds24178 := by
 decide +kernel
def cuts24179 : List PrefixCut := [⟨50,211384649,211384770⟩,
⟨128,533111986,533112289⟩]
theorem checked24179 : checkPrefixCuts (2^48) 3173122049 9 Manual.Count131072.C024179.packed 128 cuts24179 = true := by
 decide +kernel
def pointBounds24179 : List (Nat × Nat × Nat) := [(3173173248,102469533536995,102469915312220)]
theorem point_links_checked24179 : (cuts24179.take 1).map (fun c => (3173122049-1+2*2^9*c.k,102469322152346+c.lower,102469703927450+c.upper)) = pointBounds24179 := by
 decide +kernel
def cuts24180 : List PrefixCut := [⟨19,79388330,79388372⟩,
⟨116,480314007,480314272⟩,
⟨128,528920961,528921255⟩]
theorem checked24180 : checkPrefixCuts (2^48) 3173253121 9 Manual.Count131072.C024180.packed 128 cuts24180 = true := by
 decide +kernel
def pointBounds24180 : List (Nat × Nat × Nat) := [(3173272576,102469934652662,102470316428111),(3173371904,102470335578339,102470717354011)]
theorem point_links_checked24180 : (cuts24180.take 2).map (fun c => (3173253121-1+2*2^9*c.k,102469855264332+c.lower,102470237039739+c.upper)) = pointBounds24180 := by
 decide +kernel
def cuts24181 : List PrefixCut := [⟨85,353991452,353991655⟩,
⟨128,532713085,532713385⟩]
theorem checked24181 : checkPrefixCuts (2^48) 3173384193 9 Manual.Count131072.C024181.packed 128 cuts24181 = true := by
 decide +kernel
def pointBounds24181 : List (Nat × Nat × Nat) := [(3173471232,102470738176745,102471119952649)]
theorem point_links_checked24181 : (cuts24181.take 1).map (fun c => (3173384193-1+2*2^9*c.k,102470384185293+c.lower,102470765960994+c.upper)) = pointBounds24181 := by
 decide +kernel
def cuts24182 : List PrefixCut := [⟨54,218365149,218365273⟩,
⟨128,519121040,519121327⟩]
theorem checked24182 : checkPrefixCuts (2^48) 3173515265 9 Manual.Count131072.C024182.packed 128 cuts24182 = true := by
 decide +kernel
def pointBounds24182 : List (Nat × Nat × Nat) := [(3173570560,102471135263527,102471517039652)]
theorem point_links_checked24182 : (cuts24182.take 1).map (fun c => (3173515265-1+2*2^9*c.k,102470916898378+c.lower,102471298674379+c.upper)) = pointBounds24182 := by
 decide +kernel
def cuts24183 : List PrefixCut := [⟨23,94899369,94899423⟩,
⟨120,500209356,500209630⟩,
⟨128,535329716,535330009⟩]
theorem checked24183 : checkPrefixCuts (2^48) 3173646337 9 Manual.Count131072.C024183.packed 128 cuts24183 = true := by
 decide +kernel
def pointBounds24183 : List (Nat × Nat × Nat) := [(3173669888,102471530918787,102471912695129),(3173769216,102471936228774,102472318005336)]
theorem point_links_checked24183 : (cuts24183.take 2).map (fun c => (3173646337-1+2*2^9*c.k,102471436019418+c.lower,102471817795706+c.upper)) = pointBounds24183 := by
 decide +kernel
def cuts24184 : List PrefixCut := [⟨89,372926224,372926431⟩,
⟨128,534952898,534953191⟩]
theorem checked24184 : checkPrefixCuts (2^48) 3173777409 9 Manual.Count131072.C024184.packed 128 cuts24184 = true := by
 decide +kernel
def pointBounds24184 : List (Nat × Nat × Nat) := [(3173868544,102472344275358,102472726052146)]
theorem point_links_checked24184 : (cuts24184.take 1).map (fun c => (3173777409-1+2*2^9*c.k,102471971349134+c.lower,102472353125715+c.upper)) = pointBounds24184 := by
 decide +kernel
def cuts24185 : List PrefixCut := [⟨58,239355846,239355984⟩,
⟨128,531117463,531117767⟩]
theorem checked24185 : checkPrefixCuts (2^48) 3173908481 9 Manual.Count131072.C024185.packed 128 cuts24185 = true := by
 decide +kernel
def pointBounds24185 : List (Nat × Nat × Nat) := [(3173967872,102472745657878,102473127434890)]
theorem point_links_checked24185 : (cuts24185.take 1).map (fun c => (3173908481-1+2*2^9*c.k,102472506302032+c.lower,102472888078906+c.upper)) = pointBounds24185 := by
 decide +kernel
def cuts24186 : List PrefixCut := [⟨27,111204659,111204717⟩,
⟨124,514956441,514956727⟩,
⟨128,531893697,531893991⟩]
theorem checked24186 : checkPrefixCuts (2^48) 3174039553 9 Manual.Count131072.C024186.packed 128 cuts24186 = true := by
 decide +kernel
def pointBounds24186 : List (Nat × Nat × Nat) := [(3174067200,102473148624154,102473530401390),(3174166528,102473552375936,102473934153400)]
theorem point_links_checked24186 : (cuts24186.take 2).map (fun c => (3174039553-1+2*2^9*c.k,102473037419495+c.lower,102473419196673+c.upper)) = pointBounds24186 := by
 decide +kernel
def cuts24187 : List PrefixCut := [⟨93,388220708,388220925⟩,
⟨128,528590893,528591193⟩]
theorem checked24187 : checkPrefixCuts (2^48) 3174170625 9 Manual.Count131072.C024187.packed 128 cuts24187 = true := by
 decide +kernel
def pointBounds24187 : List (Nat × Nat × Nat) := [(3174265856,102473957533900,102474339311589)]
theorem point_links_checked24187 : (cuts24187.take 1).map (fun c => (3174170625-1+2*2^9*c.k,102473569313192+c.lower,102473951090664+c.upper)) = pointBounds24187 := by
 decide +kernel
def cuts24188 : List PrefixCut := [⟨62,259188648,259188794⟩,
⟨128,527770953,527771249⟩]
theorem checked24188 : checkPrefixCuts (2^48) 3174301697 9 Manual.Count131072.C024188.packed 128 cuts24188 = true := by
 decide +kernel
def pointBounds24188 : List (Nat × Nat × Nat) := [(3174365184,102474357092733,102474738870651)]
theorem point_links_checked24188 : (cuts24188.take 1).map (fun c => (3174301697-1+2*2^9*c.k,102474097904085+c.lower,102474479681857+c.upper)) = pointBounds24188 := by
 decide +kernel
def cuts24189 : List PrefixCut := [⟨31,125023158,125023230⟩,
⟨128,525443638,525443939⟩]
theorem checked24189 : checkPrefixCuts (2^48) 3174432769 9 Manual.Count131072.C024189.packed 128 cuts24189 = true := by
 decide +kernel
def pointBounds24189 : List (Nat × Nat × Nat) := [(3174464512,102474750698196,102475132476336),(3174563840,102475151118676,102475532897045)]
theorem point_links_checked24189 : (cuts24189.take 2).map (fun c => (3174432769-1+2*2^9*c.k,102474625675038+c.lower,102475007453106+c.upper)) = pointBounds24189 := by
 decide +kernel
def cuts24190 : List PrefixCut := [⟨97,408565124,408565347⟩,
⟨128,540583539,540583839⟩]
theorem checked24190 : checkPrefixCuts (2^48) 3174563841 9 Manual.Count131072.C024190.packed 128 cuts24190 = true := by
 decide +kernel
def pointBounds24190 : List (Nat × Nat × Nat) := [(3174663168,102475559683800,102475941462392)]
theorem point_links_checked24190 : (cuts24190.take 1).map (fun c => (3174563841-1+2*2^9*c.k,102475151118676+c.lower,102475532897045+c.upper)) = pointBounds24190 := by
 decide +kernel
def cuts24191 : List PrefixCut := [⟨66,268820401,268820552⟩,
⟨128,526375551,526375842⟩]
theorem checked24191 : checkPrefixCuts (2^48) 3174694913 9 Manual.Count131072.C024191.packed 128 cuts24191 = true := by
 decide +kernel
def pointBounds24191 : List (Nat × Nat × Nat) := [(3174762496,102475960522616,102476342301436)]
theorem point_links_checked24191 : (cuts24191.take 1).map (fun c => (3174694913-1+2*2^9*c.k,102475691702215+c.lower,102476073480884+c.upper)) = pointBounds24191 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000130
