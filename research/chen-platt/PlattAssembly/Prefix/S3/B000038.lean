import PlattAssemblyKernel
import PlattCertificates.Count131072.C021216
import PlattCertificates.Count131072.C021217
import PlattCertificates.Count131072.C021218
import PlattCertificates.Count131072.C021219
import PlattCertificates.Count131072.C021220
import PlattCertificates.Count131072.C021221
import PlattCertificates.Count131072.C021222
import PlattCertificates.Count131072.C021223
import PlattCertificates.Count131072.C021224
import PlattCertificates.Count131072.C021225
import PlattCertificates.Count131072.C021226
import PlattCertificates.Count131072.C021227
import PlattCertificates.Count131072.C021228
import PlattCertificates.Count131072.C021229
import PlattCertificates.Count131072.C021230
import PlattCertificates.Count131072.C021231
import PlattCertificates.Count131072.C021232
import PlattCertificates.Count131072.C021233
import PlattCertificates.Count131072.C021234
import PlattCertificates.Count131072.C021235
import PlattCertificates.Count131072.C021236
import PlattCertificates.Count131072.C021237
import PlattCertificates.Count131072.C021238
import PlattCertificates.Count131072.C021239
import PlattCertificates.Count131072.C021240
import PlattCertificates.Count131072.C021241
import PlattCertificates.Count131072.C021242
import PlattCertificates.Count131072.C021243
import PlattCertificates.Count131072.C021244
import PlattCertificates.Count131072.C021245
import PlattCertificates.Count131072.C021246
import PlattCertificates.Count131072.C021247
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts21216 : List PrefixCut := [⟨23,106635830,106635893⟩,
⟨108,504869858,504870159⟩,
⟨128,599676025,599676379⟩]
theorem checked21216 : checkPrefixCuts (2^48) 2784755713 9 Manual.Count131072.C021216.packed 128 cuts21216 = true := by
 decide +kernel
def pointBounds21216 : List (Nat × Nat × Nat) := [(2784779264,100784715850314,100785096665031),(2784866304,100785114084342,100785494899297)]
theorem point_links_checked21216 : (cuts21216.take 2).map (fun c => (2784755713-1+2*2^9*c.k,100784609214484+c.lower,100784990029138+c.upper)) = pointBounds21216 := by
 decide +kernel
def cuts21217 : List PrefixCut := [⟨65,312107535,312107716⟩,
⟨128,615111512,615111862⟩]
theorem checked21217 : checkPrefixCuts (2^48) 2784886785 9 Manual.Count131072.C021217.packed 128 cuts21217 = true := by
 decide +kernel
def pointBounds21217 : List (Nat × Nat × Nat) := [(2784953344,100785520998044,100785901813233)]
theorem point_links_checked21217 : (cuts21217.take 1).map (fun c => (2784886785-1+2*2^9*c.k,100785208890509+c.lower,100785589705517+c.upper)) = pointBounds21217 := by
 decide +kernel
def cuts21218 : List PrefixCut := [⟨22,104301280,104301341⟩,
⟨107,509370347,509370642⟩,
⟨128,611242026,611242381⟩]
theorem checked21218 : checkPrefixCuts (2^48) 2785017857 9 Manual.Count131072.C021218.packed 128 cuts21218 = true := by
 decide +kernel
def pointBounds21218 : List (Nat × Nat × Nat) := [(2785040384,100785928303301,100786309118720),(2785127424,100786333372368,100786714188021)]
theorem point_links_checked21218 : (cuts21218.take 2).map (fun c => (2785017857-1+2*2^9*c.k,100785824002021+c.lower,100786204817379+c.upper)) = pointBounds21218 := by
 decide +kernel
def cuts21219 : List PrefixCut := [⟨64,304195371,304195541⟩,
⟨128,609091058,609091406⟩]
theorem checked21219 : checkPrefixCuts (2^48) 2785148929 9 Manual.Count131072.C021219.packed 128 cuts21219 = true := by
 decide +kernel
def pointBounds21219 : List (Nat × Nat × Nat) := [(2785214464,100786739439418,100787120255301)]
theorem point_links_checked21219 : (cuts21219.take 1).map (fun c => (2785148929-1+2*2^9*c.k,100786435244047+c.lower,100786816059760+c.upper)) = pointBounds21219 := by
 decide +kernel
def cuts21220 : List PrefixCut := [⟨21,99339655,99339714⟩,
⟨106,504977132,504977435⟩,
⟨128,608961363,608961726⟩]
theorem checked21220 : checkPrefixCuts (2^48) 2785280001 9 Manual.Count131072.C021220.packed 128 cuts21220 = true := by
 decide +kernel
def pointBounds21220 : List (Nat × Nat × Nat) := [(2785301504,100787143674760,100787524490880),(2785388544,100787549312237,100787930128601)]
theorem point_links_checked21220 : (cuts21220.take 2).map (fun c => (2785280001-1+2*2^9*c.k,100787044335105+c.lower,100787425151166+c.upper)) = pointBounds21220 := by
 decide +kernel
def cuts21221 : List PrefixCut := [⟨64,308613038,308613213⟩,
⟨128,618431458,618431810⟩]
theorem checked21221 : checkPrefixCuts (2^48) 2785411073 9 Manual.Count131072.C021221.packed 128 cuts21221 = true := by
 decide +kernel
def pointBounds21221 : List (Nat × Nat × Nat) := [(2785476608,100787961909506,100788342726105)]
theorem point_links_checked21221 : (cuts21221.take 1).map (fun c => (2785411073-1+2*2^9*c.k,100787653296468+c.lower,100788034112892+c.upper)) = pointBounds21221 := by
 decide +kernel
def cuts21222 : List PrefixCut := [⟨22,100846014,100846073⟩,
⟨108,513215197,513215497⟩,
⟨128,604660130,604660485⟩]
theorem checked21222 : checkPrefixCuts (2^48) 2785542145 9 Manual.Count131072.C021222.packed 128 cuts21222 = true := by
 decide +kernel
def pointBounds21222 : List (Nat × Nat × Nat) := [(2785564672,100788372573940,100788753390775),(2785652736,100788784943123,100789165760199)]
theorem point_links_checked21222 : (cuts21222.take 2).map (fun c => (2785542145-1+2*2^9*c.k,100788271727926+c.lower,100788652544702+c.upper)) = pointBounds21222 := by
 decide +kernel
def cuts21223 : List PrefixCut := [⟨66,317677759,317677940⟩,
⟨128,610896323,610896673⟩]
theorem checked21223 : checkPrefixCuts (2^48) 2785673217 9 Manual.Count131072.C021223.packed 128 cuts21223 = true := by
 decide +kernel
def pointBounds21223 : List (Nat × Nat × Nat) := [(2785740800,100789194065815,100789574883127)]
theorem point_links_checked21223 : (cuts21223.take 1).map (fun c => (2785673217-1+2*2^9*c.k,100788876388056+c.lower,100789257205187+c.upper)) = pointBounds21223 := by
 decide +kernel
def cuts21224 : List PrefixCut := [⟨24,114981872,114981938⟩,
⟨110,529433600,529433904⟩,
⟨128,611473688,611474041⟩]
theorem checked21224 : checkPrefixCuts (2^48) 2785804289 9 Manual.Count131072.C021224.packed 128 cuts21224 = true := by
 decide +kernel
def pointBounds21224 : List (Nat × Nat × Nat) := [(2785828864,100789602266251,100789983083798),(2785916928,100790016717979,100790397535764)]
theorem point_links_checked21224 : (cuts21224.take 2).map (fun c => (2785804289-1+2*2^9*c.k,100789487284379+c.lower,100789868101860+c.upper)) = pointBounds21224 := by
 decide +kernel
def cuts21225 : List PrefixCut := [⟨68,322800401,322800589⟩,
⟨128,606393352,606393701⟩]
theorem checked21225 : checkPrefixCuts (2^48) 2785935361 9 Manual.Count131072.C021225.packed 128 cuts21225 = true := by
 decide +kernel
def pointBounds21225 : List (Nat × Nat × Nat) := [(2786004992,100790421558468,100790802376490)]
theorem point_links_checked21225 : (cuts21225.take 1).map (fun c => (2785935361-1+2*2^9*c.k,100790098758067+c.lower,100790479575901+c.upper)) = pointBounds21225 := by
 decide +kernel
def cuts21226 : List PrefixCut := [⟨26,122952310,122952383⟩,
⟨112,536253478,536253785⟩,
⟨128,611820208,611820562⟩]
theorem checked21226 : checkPrefixCuts (2^48) 2786066433 9 Manual.Count131072.C021226.packed 128 cuts21226 = true := by
 decide +kernel
def pointBounds21226 : List (Nat × Nat × Nat) := [(2786093056,100790828103729,100791208921985),(2786181120,100791241404897,100791622223387)]
theorem point_links_checked21226 : (cuts21226.take 2).map (fun c => (2786066433-1+2*2^9*c.k,100790705151419+c.lower,100791085969602+c.upper)) = pointBounds21226 := by
 decide +kernel
def cuts21227 : List PrefixCut := [⟨70,337014193,337014384⟩,
⟨128,612397629,612397975⟩]
theorem checked21227 : checkPrefixCuts (2^48) 2786197505 9 Manual.Count131072.C021227.packed 128 cuts21227 = true := by
 decide +kernel
def pointBounds21227 : List (Nat × Nat × Nat) := [(2786269184,100791653985820,100792034804548)]
theorem point_links_checked21227 : (cuts21227.take 1).map (fun c => (2786197505-1+2*2^9*c.k,100791316971627+c.lower,100791697790164+c.upper)) = pointBounds21227 := by
 decide +kernel
def cuts21228 : List PrefixCut := [⟨28,130921230,130921303⟩,
⟨114,540041492,540041801⟩,
⟨128,604590391,604590738⟩]
theorem checked21228 : checkPrefixCuts (2^48) 2786328577 9 Manual.Count131072.C021228.packed 128 cuts21228 = true := by
 decide +kernel
def pointBounds21228 : List (Nat × Nat × Nat) := [(2786357248,100792060290486,100792441109442),(2786445312,100792469410748,100792850229940)]
theorem point_links_checked21228 : (cuts21228.take 2).map (fun c => (2786328577-1+2*2^9*c.k,100791929369256+c.lower,100792310188139+c.upper)) = pointBounds21228 := by
 decide +kernel
def cuts21229 : List PrefixCut := [⟨72,342235085,342235282⟩,
⟨128,613956098,613956452⟩]
theorem checked21229 : checkPrefixCuts (2^48) 2786459649 9 Manual.Count131072.C021229.packed 128 cuts21229 = true := by
 decide +kernel
def pointBounds21229 : List (Nat × Nat × Nat) := [(2786533376,100792876194732,100793257014159)]
theorem point_links_checked21229 : (cuts21229.take 1).map (fun c => (2786459649-1+2*2^9*c.k,100792533959647+c.lower,100792914778877+c.upper)) = pointBounds21229 := by
 decide +kernel
def cuts21230 : List PrefixCut := [⟨30,140807843,140807923⟩,
⟨116,550394330,550394644⟩,
⟨128,607563703,607564050⟩]
theorem checked21230 : checkPrefixCuts (2^48) 2786590721 9 Manual.Count131072.C021230.packed 128 cuts21230 = true := by
 decide +kernel
def pointBounds21230 : List (Nat × Nat × Nat) := [(2786621440,100793288723588,100793669543252),(2786709504,100793698310075,100794079129973)]
theorem point_links_checked21230 : (cuts21230.take 2).map (fun c => (2786590721-1+2*2^9*c.k,100793147915745+c.lower,100793528735329+c.upper)) = pointBounds21230 := by
 decide +kernel
def cuts21231 : List PrefixCut := [⟨74,348162003,348162206⟩,
⟨128,604909077,604909430⟩]
theorem checked21231 : checkPrefixCuts (2^48) 2786721793 9 Manual.Count131072.C021231.packed 128 cuts21231 = true := by
 decide +kernel
def pointBounds21231 : List (Nat × Nat × Nat) := [(2786797568,100794103641451,100794484461585)]
theorem point_links_checked21231 : (cuts21231.take 1).map (fun c => (2786721793-1+2*2^9*c.k,100793755479448+c.lower,100794136299379+c.upper)) = pointBounds21231 := by
 decide +kernel
def cuts21232 : List PrefixCut := [⟨32,148571600,148571689⟩,
⟨118,558523343,558523671⟩,
⟨128,605587679,605588033⟩]
theorem checked21232 : checkPrefixCuts (2^48) 2786852865 9 Manual.Count131072.C021232.packed 128 cuts21232 = true := by
 decide +kernel
def pointBounds21232 : List (Nat × Nat × Nat) := [(2786885632,100794508960125,100794889780498),(2786973696,100794918911868,100795299732480)]
theorem point_links_checked21232 : (cuts21232.take 2).map (fun c => (2786852865-1+2*2^9*c.k,100794360388525+c.lower,100794741208809+c.upper)) = pointBounds21232 := by
 decide +kernel
def cuts21233 : List PrefixCut := [⟨76,365601271,365601487⟩,
⟨128,617072478,617072840⟩]
theorem checked21233 : checkPrefixCuts (2^48) 2786983937 9 Manual.Count131072.C021233.packed 128 cuts21233 = true := by
 decide +kernel
def pointBounds21233 : List (Nat × Nat × Nat) := [(2787061760,100795331577475,100795712398329)]
theorem point_links_checked21233 : (cuts21233.take 1).map (fun c => (2786983937-1+2*2^9*c.k,100794965976204+c.lower,100795346796842+c.upper)) = pointBounds21233 := by
 decide +kernel
def cuts21234 : List PrefixCut := [⟨34,162898258,162898350⟩,
⟨120,564227068,564227400⟩,
⟨128,600986297,600986648⟩]
theorem checked21234 : checkPrefixCuts (2^48) 2787115009 9 Manual.Count131072.C021234.packed 128 cuts21234 = true := by
 decide +kernel
def pointBounds21234 : List (Nat × Nat × Nat) := [(2787149824,100795745946940,100796126768032),(2787237888,100796147275750,100796528097082)]
theorem point_links_checked21234 : (cuts21234.take 2).map (fun c => (2787115009-1+2*2^9*c.k,100795583048682+c.lower,100795963869682+c.upper)) = pointBounds21234 := by
 decide +kernel
def cuts21235 : List PrefixCut := [⟨78,376170185,376170405⟩,
⟨128,613581004,613581361⟩]
theorem checked21235 : checkPrefixCuts (2^48) 2787246081 9 Manual.Count131072.C021235.packed 128 cuts21235 = true := by
 decide +kernel
def pointBounds21235 : List (Nat × Nat × Nat) := [(2787325952,100796560205164,100796941026735)]
theorem point_links_checked21235 : (cuts21235.take 1).map (fun c => (2787246081-1+2*2^9*c.k,100796184034979+c.lower,100796564856330+c.upper)) = pointBounds21235 := by
 decide +kernel
def cuts21236 : List PrefixCut := [⟨36,169345685,169345782⟩,
⟨122,576089371,576089705⟩,
⟨128,604968894,604969244⟩]
theorem checked21236 : checkPrefixCuts (2^48) 2787377153 9 Manual.Count131072.C021236.packed 128 cuts21236 = true := by
 decide +kernel
def pointBounds21236 : List (Nat × Nat × Nat) := [(2787414016,100796966961668,100797347783473),(2787502080,100797373705354,100797754527396)]
theorem point_links_checked21236 : (cuts21236.take 2).map (fun c => (2787377153-1+2*2^9*c.k,100796797615983+c.lower,100797178437691+c.upper)) = pointBounds21236 := by
 decide +kernel
def cuts21237 : List PrefixCut := [⟨80,383909830,383910052⟩,
⟨128,612210629,612210988⟩]
theorem checked21237 : checkPrefixCuts (2^48) 2787508225 9 Manual.Count131072.C021237.packed 128 cuts21237 = true := by
 decide +kernel
def pointBounds21237 : List (Nat × Nat × Nat) := [(2787590144,100797786494707,100798167316987)]
theorem point_links_checked21237 : (cuts21237.take 1).map (fun c => (2787508225-1+2*2^9*c.k,100797402584877+c.lower,100797783406935+c.upper)) = pointBounds21237 := by
 decide +kernel
def cuts21238 : List PrefixCut := [⟨38,180739501,180739606⟩,
⟨124,586636903,586637246⟩,
⟨128,607234339,607234694⟩]
theorem checked21238 : checkPrefixCuts (2^48) 2787639297 9 Manual.Count131072.C021238.packed 128 cuts21238 = true := by
 decide +kernel
def pointBounds21238 : List (Nat × Nat × Nat) := [(2787678208,100798195535007,100798576357529),(2787766272,100798601432409,100798982255169)]
theorem point_links_checked21238 : (cuts21238.take 2).map (fun c => (2787639297-1+2*2^9*c.k,100798014795506+c.lower,100798395617923+c.upper)) = pointBounds21238 := by
 decide +kernel
def cuts21239 : List PrefixCut := [⟨82,390739256,390739482⟩,
⟨128,611244337,611244690⟩]
theorem checked21239 : checkPrefixCuts (2^48) 2787770369 9 Manual.Count131072.C021239.packed 128 cuts21239 = true := by
 decide +kernel
def pointBounds21239 : List (Nat × Nat × Nat) := [(2787854336,100799012769101,100799393592099)]
theorem point_links_checked21239 : (cuts21239.take 1).map (fun c => (2787770369-1+2*2^9*c.k,100798622029845+c.lower,100799002852617+c.upper)) = pointBounds21239 := by
 decide +kernel
def cuts21240 : List PrefixCut := [⟨40,191222494,191222607⟩,
⟨126,602735100,602735449⟩,
⟨128,612225180,612225534⟩]
theorem checked21240 : checkPrefixCuts (2^48) 2787901441 9 Manual.Count131072.C021240.packed 128 cuts21240 = true := by
 decide +kernel
def pointBounds21240 : List (Nat × Nat × Nat) := [(2787942400,100799424496676,100799805319914),(2788030464,100799836009282,100800216832756)]
theorem point_links_checked21240 : (cuts21240.take 2).map (fun c => (2787901441-1+2*2^9*c.k,100799233274182+c.lower,100799614097307+c.upper)) = pointBounds21240 := by
 decide +kernel
def cuts21241 : List PrefixCut := [⟨84,400798131,400798359⟩,
⟨128,605735437,605735787⟩]
theorem checked21241 : checkPrefixCuts (2^48) 2788032513 9 Manual.Count131072.C021241.packed 128 cuts21241 = true := by
 decide +kernel
def pointBounds21241 : List (Nat × Nat × Nat) := [(2788118528,100800246297493,100800627121200)]
theorem point_links_checked21241 : (cuts21241.take 1).map (fun c => (2788032513-1+2*2^9*c.k,100799845499362+c.lower,100800226322841+c.upper)) = pointBounds21241 := by
 decide +kernel
def cuts21242 : List PrefixCut := [⟨42,200391170,200391286⟩,
⟨128,610552481,610552831⟩]
theorem checked21242 : checkPrefixCuts (2^48) 2788163585 9 Manual.Count131072.C021242.packed 128 cuts21242 = true := by
 decide +kernel
def pointBounds21242 : List (Nat × Nat × Nat) := [(2788206592,100800651625969,100801032449914),(2788294656,100801061787280,100801442611459)]
theorem point_links_checked21242 : (cuts21242.take 2).map (fun c => (2788163585-1+2*2^9*c.k,100800451234799+c.lower,100800832058628+c.upper)) = pointBounds21242 := by
 decide +kernel
def cuts21243 : List PrefixCut := [⟨86,411056839,411057072⟩,
⟨128,608807667,608808016⟩]
theorem checked21243 : checkPrefixCuts (2^48) 2788294657 9 Manual.Count131072.C021243.packed 128 cuts21243 = true := by
 decide +kernel
def pointBounds21243 : List (Nat × Nat × Nat) := [(2788382720,100801472844119,100801853668531)]
theorem point_links_checked21243 : (cuts21243.take 1).map (fun c => (2788294657-1+2*2^9*c.k,100801061787280+c.lower,100801442611459+c.upper)) = pointBounds21243 := by
 decide +kernel
def cuts21244 : List PrefixCut := [⟨44,207034505,207034626⟩,
⟨128,611807229,611807584⟩]
theorem checked21244 : checkPrefixCuts (2^48) 2788425729 9 Manual.Count131072.C021244.packed 128 cuts21244 = true := by
 decide +kernel
def pointBounds21244 : List (Nat × Nat × Nat) := [(2788470784,100801877629452,100802258454101)]
theorem point_links_checked21244 : (cuts21244.take 1).map (fun c => (2788425729-1+2*2^9*c.k,100801670594947+c.lower,100802051419475+c.upper)) = pointBounds21244 := by
 decide +kernel
def cuts21245 : List PrefixCut := [⟨2,9892046,9892051⟩,
⟨88,416065019,416065260⟩,
⟨128,602997163,602997510⟩]
theorem checked21245 : checkPrefixCuts (2^48) 2788556801 9 Manual.Count131072.C021245.packed 128 cuts21245 = true := by
 decide +kernel
def pointBounds21245 : List (Nat × Nat × Nat) := [(2788558848,100802292294222,100802673119110),(2788646912,100802698467195,100803079292319)]
theorem point_links_checked21245 : (cuts21245.take 2).map (fun c => (2788556801-1+2*2^9*c.k,100802282402176+c.lower,100802663227059+c.upper)) = pointBounds21245 := by
 decide +kernel
def cuts21246 : List PrefixCut := [⟨46,216099002,216099129⟩,
⟨128,610134741,610135090⟩]
theorem checked21246 : checkPrefixCuts (2^48) 2788687873 9 Manual.Count131072.C021246.packed 128 cuts21246 = true := by
 decide +kernel
def pointBounds21246 : List (Nat × Nat × Nat) := [(2788734976,100803101498341,100803482323698)]
theorem point_links_checked21246 : (cuts21246.take 1).map (fun c => (2788687873-1+2*2^9*c.k,100802885399339+c.lower,100803266224569+c.upper)) = pointBounds21246 := by
 decide +kernel
def cuts21247 : List PrefixCut := [⟨4,17057121,17057130⟩,
⟨90,421778589,421778834⟩,
⟨128,603545883,603546230⟩]
theorem checked21247 : checkPrefixCuts (2^48) 2788818945 9 Manual.Count131072.C021247.packed 128 cuts21247 = true := by
 decide +kernel
def pointBounds21247 : List (Nat × Nat × Nat) := [(2788823040,100803512591201,100803893416789),(2788911104,100803917312669,100804298138493)]
theorem point_links_checked21247 : (cuts21247.take 2).map (fun c => (2788818945-1+2*2^9*c.k,100803495534080+c.lower,100803876359659+c.upper)) = pointBounds21247 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000038
