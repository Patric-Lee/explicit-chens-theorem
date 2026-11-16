import PlattAssemblyKernel
import PlattCertificates.Count131072.C017456
import PlattCertificates.Count131072.C017457
import PlattCertificates.Count131072.C017458
import PlattCertificates.Count131072.C017459
import PlattCertificates.Count131072.C017460
import PlattCertificates.Count131072.C017461
import PlattCertificates.Count131072.C017462
import PlattCertificates.Count131072.C017463
import PlattCertificates.Count131072.C017464
import PlattCertificates.Count131072.C017465
import PlattCertificates.Count131072.C017466
import PlattCertificates.Count131072.C017467
import PlattCertificates.Count131072.C017468
import PlattCertificates.Count131072.C017469
import PlattCertificates.Count131072.C017470
import PlattCertificates.Count131072.C017471
import PlattCertificates.Count131072.C017472
import PlattCertificates.Count131072.C017473
import PlattCertificates.Count131072.C017474
import PlattCertificates.Count131072.C017475
import PlattCertificates.Count131072.C017476
import PlattCertificates.Count131072.C017477
import PlattCertificates.Count131072.C017478
import PlattCertificates.Count131072.C017479
import PlattCertificates.Count131072.C017480
import PlattCertificates.Count131072.C017481
import PlattCertificates.Count131072.C017482
import PlattCertificates.Count131072.C017483
import PlattCertificates.Count131072.C017484
import PlattCertificates.Count131072.C017485
import PlattCertificates.Count131072.C017486
import PlattCertificates.Count131072.C017487
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000233
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts17456 : List PrefixCut := [⟨58,336008133,336008340⟩,
⟨128,742251968,742252429⟩]
theorem checked17456 : checkPrefixCuts (2^48) 2291924993 9 Manual.Count131072.C017456.packed 128 cuts17456 = true := by
 decide +kernel
def pointBounds17456 : List (Nat × Nat × Nat) := [(2291984384,98252849480550,98253228785691),(2292056064,98253255724385,98253635029780)]
theorem point_links_checked17456 : (cuts17456.take 2).map (fun c => (2291924993-1+2*2^9*c.k,98252513472417+c.lower,98252892777351+c.upper)) = pointBounds17456 := by
 decide +kernel
def cuts17457 : List PrefixCut := [⟨70,413476403,413476652⟩,
⟨128,746998695,746999151⟩]
theorem checked17457 : checkPrefixCuts (2^48) 2292056065 9 Manual.Count131072.C017457.packed 128 cuts17457 = true := by
 decide +kernel
def pointBounds17457 : List (Nat × Nat × Nat) := [(2292127744,98253669200788,98254048506432)]
theorem point_links_checked17457 : (cuts17457.take 1).map (fun c => (2292056065-1+2*2^9*c.k,98253255724385+c.lower,98253635029780+c.upper)) = pointBounds17457 := by
 decide +kernel
def cuts17458 : List PrefixCut := [⟨12,73678315,73678360⟩,
⟨82,479392790,479393091⟩,
⟨128,755183017,755183487⟩]
theorem checked17458 : checkPrefixCuts (2^48) 2292187137 9 Manual.Count131072.C017458.packed 128 cuts17458 = true := by
 decide +kernel
def pointBounds17458 : List (Nat × Nat × Nat) := [(2292199424,98254076401395,98254455707291),(2292271104,98254482115870,98254861422022)]
theorem point_links_checked17458 : (cuts17458.take 2).map (fun c => (2292187137-1+2*2^9*c.k,98254002723080+c.lower,98254382028931+c.upper)) = pointBounds17458 := by
 decide +kernel
def cuts17459 : List PrefixCut := [⟨24,142436201,142436290⟩,
⟨94,549598770,549599112⟩,
⟨128,746790530,746790995⟩]
theorem checked17459 : checkPrefixCuts (2^48) 2292318209 9 Manual.Count131072.C017459.packed 128 cuts17459 = true := by
 decide +kernel
def pointBounds17459 : List (Nat × Nat × Nat) := [(2292342784,98254900342298,98255279648708),(2292414464,98255307504867,98255686811530)]
theorem point_links_checked17459 : (cuts17459.take 2).map (fun c => (2292318209-1+2*2^9*c.k,98254757906097+c.lower,98255137212418+c.upper)) = pointBounds17459 := by
 decide +kernel
def cuts17460 : List PrefixCut := [⟨36,202099959,202100085⟩,
⟨106,610341999,610342373⟩,
⟨128,737539021,737539475⟩]
theorem checked17460 : checkPrefixCuts (2^48) 2292449281 9 Manual.Count131072.C017460.packed 128 cuts17460 = true := by
 decide +kernel
def pointBounds17460 : List (Nat × Nat × Nat) := [(2292486144,98255706796586,98256086103498),(2292557824,98256115038626,98256494345786)]
theorem point_links_checked17460 : (cuts17460.take 2).map (fun c => (2292449281-1+2*2^9*c.k,98255504696627+c.lower,98255884003413+c.upper)) = pointBounds17460 := by
 decide +kernel
def cuts17461 : List PrefixCut := [⟨48,277226251,277226423⟩,
⟨118,687898248,687898675⟩,
⟨128,747318784,747319249⟩]
theorem checked17461 : checkPrefixCuts (2^48) 2292580353 9 Manual.Count131072.C017461.packed 128 cuts17461 = true := by
 decide +kernel
def pointBounds17461 : List (Nat × Nat × Nat) := [(2292629504,98256519461899,98256898769311),(2292701184,98256930133896,98257309441563)]
theorem point_links_checked17461 : (cuts17461.take 2).map (fun c => (2292580353-1+2*2^9*c.k,98256242235648+c.lower,98256621542888+c.upper)) = pointBounds17461 := by
 decide +kernel
def cuts17462 : List PrefixCut := [⟨60,350133719,350133933⟩,
⟨128,748381124,748381585⟩]
theorem checked17462 : checkPrefixCuts (2^48) 2292711425 9 Manual.Count131072.C017462.packed 128 cuts17462 = true := by
 decide +kernel
def pointBounds17462 : List (Nat × Nat × Nat) := [(2292772864,98257339688151,98257718996070)]
theorem point_links_checked17462 : (cuts17462.take 1).map (fun c => (2292711425-1+2*2^9*c.k,98256989554432+c.lower,98257368862137+c.upper)) = pointBounds17462 := by
 decide +kernel
def cuts17463 : List PrefixCut := [⟨2,11048613,11048620⟩,
⟨72,419226893,419227148⟩,
⟨128,744655513,744655970⟩]
theorem checked17463 : checkPrefixCuts (2^48) 2292842497 9 Manual.Count131072.C017463.packed 128 cuts17463 = true := by
 decide +kernel
def pointBounds17463 : List (Nat × Nat × Nat) := [(2292844544,98257748984169,98258128292342),(2292916224,98258157162449,98258536470870)]
theorem point_links_checked17463 : (cuts17463.take 2).map (fun c => (2292842497-1+2*2^9*c.k,98257737935556+c.lower,98258117243722+c.upper)) = pointBounds17463 := by
 decide +kernel
def cuts17464 : List PrefixCut := [⟨14,81263824,81263873⟩,
⟨84,485488602,485488901⟩,
⟨128,746576984,746577446⟩]
theorem checked17464 : checkPrefixCuts (2^48) 2292973569 9 Manual.Count131072.C017464.packed 128 cuts17464 = true := by
 decide +kernel
def pointBounds17464 : List (Nat × Nat × Nat) := [(2292987904,98258563854893,98258943163565),(2293059584,98258968079671,98259347388593)]
theorem point_links_checked17464 : (cuts17464.take 2).map (fun c => (2292973569-1+2*2^9*c.k,98258482591069+c.lower,98258861899692+c.upper)) = pointBounds17464 := by
 decide +kernel
def cuts17465 : List PrefixCut := [⟨26,150856879,150856973⟩,
⟨96,558124974,558125324⟩,
⟨128,744693206,744693668⟩]
theorem checked17465 : checkPrefixCuts (2^48) 2293104641 9 Manual.Count131072.C017465.packed 128 cuts17465 = true := by
 decide +kernel
def pointBounds17465 : List (Nat × Nat × Nat) := [(2293131264,98259380024932,98259759334111),(2293202944,98259787293027,98260166602462)]
theorem point_links_checked17465 : (cuts17465.take 2).map (fun c => (2293104641-1+2*2^9*c.k,98259229168053+c.lower,98259608477138+c.upper)) = pointBounds17465 := by
 decide +kernel
def cuts17466 : List PrefixCut := [⟨38,223141935,223142071⟩,
⟨108,638362385,638362778⟩,
⟨128,756678846,756679310⟩]
theorem checked17466 : checkPrefixCuts (2^48) 2293235713 9 Manual.Count131072.C017466.packed 128 cuts17466 = true := by
 decide +kernel
def pointBounds17466 : List (Nat × Nat × Nat) := [(2293274624,98260197003194,98260576312877),(2293346304,98260612223644,98260991533584)]
theorem point_links_checked17466 : (cuts17466.take 2).map (fun c => (2293235713-1+2*2^9*c.k,98259973861259+c.lower,98260353170806+c.upper)) = pointBounds17466 := by
 decide +kernel
def cuts17467 : List PrefixCut := [⟨50,291368105,291368287⟩,
⟨120,694044200,694044632⟩,
⟨128,740435217,740435678⟩]
theorem checked17467 : checkPrefixCuts (2^48) 2293366785 9 Manual.Count131072.C017467.packed 128 cuts17467 = true := by
 decide +kernel
def pointBounds17467 : List (Nat × Nat × Nat) := [(2293417984,98261021908210,98261401218403),(2293489664,98261424584305,98261803894748)]
theorem point_links_checked17467 : (cuts17467.take 2).map (fun c => (2293366785-1+2*2^9*c.k,98260730540105+c.lower,98261109850116+c.upper)) = pointBounds17467 := by
 decide +kernel
def cuts17468 : List PrefixCut := [⟨62,362408804,362409025⟩,
⟨128,750701591,750702052⟩]
theorem checked17468 : checkPrefixCuts (2^48) 2293497857 9 Manual.Count131072.C017468.packed 128 cuts17468 = true := by
 decide +kernel
def pointBounds17468 : List (Nat × Nat × Nat) := [(2293561344,98261833384126,98262212694819)]
theorem point_links_checked17468 : (cuts17468.take 1).map (fun c => (2293497857-1+2*2^9*c.k,98261470975322+c.lower,98261850285794+c.upper)) = pointBounds17468 := by
 decide +kernel
def cuts17469 : List PrefixCut := [⟨4,23930442,23930457⟩,
⟨74,427796077,427796341⟩,
⟨128,742559484,742559939⟩]
theorem checked17469 : checkPrefixCuts (2^48) 2293628929 9 Manual.Count131072.C017469.packed 128 cuts17469 = true := by
 decide +kernel
def pointBounds17469 : List (Nat × Nat × Nat) := [(2293633024,98262245607355,98262624918303),(2293704704,98262649472990,98263028784187)]
theorem point_links_checked17469 : (cuts17469.take 2).map (fun c => (2293628929-1+2*2^9*c.k,98262221676913+c.lower,98262600987846+c.upper)) = pointBounds17469 := by
 decide +kernel
def cuts17470 : List PrefixCut := [⟨16,90684817,90684874⟩,
⟨86,498451877,498452184⟩,
⟨128,747425309,747425767⟩]
theorem checked17470 : checkPrefixCuts (2^48) 2293760001 9 Manual.Count131072.C017470.packed 128 cuts17470 = true := by
 decide +kernel
def pointBounds17470 : List (Nat × Nat × Nat) := [(2293776384,98263054921214,98263434232659),(2293848064,98263462688274,98263841999969)]
theorem point_links_checked17470 : (cuts17470.take 2).map (fun c => (2293760001-1+2*2^9*c.k,98262964236397+c.lower,98263343547785+c.upper)) = pointBounds17470 := by
 decide +kernel
def cuts17471 : List PrefixCut := [⟨29,168842770,168842871⟩,
⟨100,585786766,585787122⟩,
⟨128,747137334,747137791⟩]
theorem checked17471 : checkPrefixCuts (2^48) 2293891073 9 Manual.Count131072.C017471.packed 128 cuts17471 = true := by
 decide +kernel
def pointBounds17471 : List (Nat × Nat × Nat) := [(2293920768,98263880504476,98264259816423),(2293993472,98264297448472,98264676760674)]
theorem point_links_checked17471 : (cuts17471.take 2).map (fun c => (2293891073-1+2*2^9*c.k,98263711661706+c.lower,98264090973552+c.upper)) = pointBounds17471 := by
 decide +kernel
def cuts17472 : List PrefixCut := [⟨43,250058760,250058915⟩,
⟨114,660718886,660719299⟩,
⟨128,745008749,745009214⟩]
theorem checked17472 : checkPrefixCuts (2^48) 2294022145 9 Manual.Count131072.C017472.packed 128 cuts17472 = true := by
 decide +kernel
def pointBounds17472 : List (Nat × Nat × Nat) := [(2294066176,98264708857800,98265088170258),(2294138880,98265119517926,98265498830642)]
theorem point_links_checked17472 : (cuts17472.take 2).map (fun c => (2294022145-1+2*2^9*c.k,98264458799040+c.lower,98264838111343+c.upper)) = pointBounds17472 := by
 decide +kernel
def cuts17473 : List PrefixCut := [⟨57,337767491,337767695⟩,
⟨128,747910787,747911250⟩]
theorem checked17473 : checkPrefixCuts (2^48) 2294153217 9 Manual.Count131072.C017473.packed 128 cuts17473 = true := by
 decide +kernel
def pointBounds17473 : List (Nat × Nat × Nat) := [(2294211584,98265541575280,98265920888252),(2294284288,98265951718576,98266331031807)]
theorem point_links_checked17473 : (cuts17473.take 2).map (fun c => (2294153217-1+2*2^9*c.k,98265203807789+c.lower,98265583120557+c.upper)) = pointBounds17473 := by
 decide +kernel
def cuts17474 : List PrefixCut := [⟨71,409148983,409149239⟩,
⟨128,747254563,747255031⟩]
theorem checked17474 : checkPrefixCuts (2^48) 2294284289 9 Manual.Count131072.C017474.packed 128 cuts17474 = true := by
 decide +kernel
def pointBounds17474 : List (Nat × Nat × Nat) := [(2294356992,98266360867559,98266740181046)]
theorem point_links_checked17474 : (cuts17474.take 1).map (fun c => (2294284289-1+2*2^9*c.k,98265951718576+c.lower,98266331031807+c.upper)) = pointBounds17474 := by
 decide +kernel
def cuts17475 : List PrefixCut := [⟨14,82807568,82807618⟩,
⟨85,496101506,496101812⟩,
⟨128,746230616,746231078⟩]
theorem checked17475 : checkPrefixCuts (2^48) 2294415361 9 Manual.Count131072.C017475.packed 128 cuts17475 = true := by
 decide +kernel
def pointBounds17475 : List (Nat × Nat × Nat) := [(2294429696,98266781780707,98267161094456),(2294502400,98267195074645,98267574388650)]
theorem point_links_checked17475 : (cuts17475.take 2).map (fun c => (2294415361-1+2*2^9*c.k,98266698973139+c.lower,98267078286838+c.upper)) = pointBounds17475 := by
 decide +kernel
def cuts17476 : List PrefixCut := [⟨28,162783768,162783873⟩,
⟨99,580835512,580835870⟩,
⟨128,750481237,750481703⟩]
theorem checked17476 : checkPrefixCuts (2^48) 2294546433 9 Manual.Count131072.C017476.packed 128 cuts17476 = true := by
 decide +kernel
def pointBounds17476 : List (Nat × Nat × Nat) := [(2294575104,98267607987523,98267987301789),(2294647808,98268026039267,98268405353786)]
theorem point_links_checked17476 : (cuts17476.take 2).map (fun c => (2294546433-1+2*2^9*c.k,98267445203755+c.lower,98267824517916+c.upper)) = pointBounds17476 := by
 decide +kernel
def cuts17477 : List PrefixCut := [⟨42,244712888,244713036⟩,
⟨113,662615554,662615962⟩,
⟨128,746390733,746391194⟩]
theorem checked17477 : checkPrefixCuts (2^48) 2294677505 9 Manual.Count131072.C017477.packed 128 cuts17477 = true := by
 decide +kernel
def pointBounds17477 : List (Nat × Nat × Nat) := [(2294720512,98268440397880,98268819712655),(2294793216,98268858300546,98269237615581)]
theorem point_links_checked17477 : (cuts17477.take 2).map (fun c => (2294677505-1+2*2^9*c.k,98268195684992+c.lower,98268574999619+c.upper)) = pointBounds17477 := by
 decide +kernel
def cuts17478 : List PrefixCut := [⟨56,327613365,327613571⟩,
⟨127,745734744,745735209⟩,
⟨128,751499306,751499775⟩]
theorem checked17478 : checkPrefixCuts (2^48) 2294808577 9 Manual.Count131072.C017478.packed 128 cuts17478 = true := by
 decide +kernel
def pointBounds17478 : List (Nat × Nat × Nat) := [(2294865920,98269269689090,98269649004384),(2294938624,98269687810469,98270067126022)]
theorem point_links_checked17478 : (cuts17478.take 2).map (fun c => (2294808577-1+2*2^9*c.k,98268942075725+c.lower,98269321390813+c.upper)) = pointBounds17478 := by
 decide +kernel
def cuts17479 : List PrefixCut := [⟨70,404616786,404617036⟩,
⟨128,747163686,747164149⟩]
theorem checked17479 : checkPrefixCuts (2^48) 2294939649 9 Manual.Count131072.C017479.packed 128 cuts17479 = true := by
 decide +kernel
def pointBounds17479 : List (Nat × Nat × Nat) := [(2295011328,98270098191817,98270477507624)]
theorem point_links_checked17479 : (cuts17479.take 1).map (fun c => (2294939649-1+2*2^9*c.k,98269693575031+c.lower,98270072890588+c.upper)) = pointBounds17479 := by
 decide +kernel
def cuts17480 : List PrefixCut := [⟨13,72604580,72604626⟩,
⟨84,485044880,485045180⟩,
⟨128,735838443,735838901⟩]
theorem checked17480 : checkPrefixCuts (2^48) 2295070721 9 Manual.Count131072.C017480.packed 128 cuts17480 = true := by
 decide +kernel
def pointBounds17480 : List (Nat × Nat × Nat) := [(2295084032,98270513343297,98270892659363),(2295156736,98270925783597,98271305099917)]
theorem point_links_checked17480 : (cuts17480.take 2).map (fun c => (2295070721-1+2*2^9*c.k,98270440738717+c.lower,98270820054737+c.upper)) = pointBounds17480 := by
 decide +kernel
def cuts17481 : List PrefixCut := [⟨27,157586614,157586715⟩,
⟨98,575273975,575274334⟩,
⟨128,749040747,749041213⟩]
theorem checked17481 : checkPrefixCuts (2^48) 2295201793 9 Manual.Count131072.C017481.packed 128 cuts17481 = true := by
 decide +kernel
def pointBounds17481 : List (Nat × Nat × Nat) := [(2295229440,98271334163774,98271713480353),(2295302144,98271751851135,98272131167972)]
theorem point_links_checked17481 : (cuts17481.take 2).map (fun c => (2295201793-1+2*2^9*c.k,98271176577160+c.lower,98271555893638+c.upper)) = pointBounds17481 := by
 decide +kernel
def cuts17482 : List PrefixCut := [⟨41,237162737,237162881⟩,
⟨112,648201834,648202230⟩,
⟨128,739555712,739556166⟩]
theorem checked17482 : checkPrefixCuts (2^48) 2295332865 9 Manual.Count131072.C017482.packed 128 cuts17482 = true := by
 decide +kernel
def pointBounds17482 : List (Nat × Nat × Nat) := [(2295374848,98272162780644,98272542097732),(2295447552,98272573819741,98272953137081)]
theorem point_links_checked17482 : (cuts17482.take 2).map (fun c => (2295332865-1+2*2^9*c.k,98271925617907+c.lower,98272304934851+c.upper)) = pointBounds17482 := by
 decide +kernel
def cuts17483 : List PrefixCut := [⟨55,323473449,323473651⟩,
⟨126,733996171,733996624⟩,
⟨128,745399392,745399852⟩]
theorem checked17483 : checkPrefixCuts (2^48) 2295463937 9 Manual.Count131072.C017483.packed 128 cuts17483 = true := by
 decide +kernel
def pointBounds17483 : List (Nat × Nat × Nat) := [(2295520256,98272988647068,98273367964668),(2295592960,98273399169790,98273778487641)]
theorem point_links_checked17483 : (cuts17483.take 2).map (fun c => (2295463937-1+2*2^9*c.k,98272665173619+c.lower,98273044491017+c.upper)) = pointBounds17483 := by
 decide +kernel
def cuts17484 : List PrefixCut := [⟨69,405237063,405237309⟩,
⟨128,749402866,749403323⟩]
theorem checked17484 : checkPrefixCuts (2^48) 2295595009 9 Manual.Count131072.C017484.packed 128 cuts17484 = true := by
 decide +kernel
def pointBounds17484 : List (Nat × Nat × Nat) := [(2295665664,98273815810074,98274195128178)]
theorem point_links_checked17484 : (cuts17484.take 1).map (fun c => (2295595009-1+2*2^9*c.k,98273410573011+c.lower,98273789890869+c.upper)) = pointBounds17484 := by
 decide +kernel
def cuts17485 : List PrefixCut := [⟨12,67924769,67924813⟩,
⟨83,476446697,476447001⟩,
⟨128,744455650,744456122⟩]
theorem checked17485 : checkPrefixCuts (2^48) 2295726081 9 Manual.Count131072.C017485.packed 128 cuts17485 = true := by
 decide +kernel
def pointBounds17485 : List (Nat × Nat × Nat) := [(2295738368,98274227900646,98274607219005),(2295811072,98274636422574,98275015741193)]
theorem point_links_checked17485 : (cuts17485.take 2).map (fun c => (2295726081-1+2*2^9*c.k,98274159975877+c.lower,98274539294192+c.upper)) = pointBounds17485 := by
 decide +kernel
def cuts17486 : List PrefixCut := [⟨26,150553435,150553528⟩,
⟨97,567508728,567509078⟩,
⟨128,754711413,754711876⟩]
theorem checked17486 : checkPrefixCuts (2^48) 2295857153 9 Manual.Count131072.C017486.packed 128 cuts17486 = true := by
 decide +kernel
def pointBounds17486 : List (Nat × Nat × Nat) := [(2295883776,98275054984962,98275434303842),(2295956480,98275471940255,98275851259392)]
theorem point_links_checked17486 : (cuts17486.take 2).map (fun c => (2295857153-1+2*2^9*c.k,98274904431527+c.lower,98275283750314+c.upper)) = pointBounds17486 := by
 decide +kernel
def cuts17487 : List PrefixCut := [⟨40,230720271,230720412⟩,
⟨111,653410918,653411312⟩,
⟨128,752216591,752217051⟩]
theorem checked17487 : checkPrefixCuts (2^48) 2295988225 9 Manual.Count131072.C017487.packed 128 cuts17487 = true := by
 decide +kernel
def pointBounds17487 : List (Nat × Nat × Nat) := [(2296029184,98275889863211,98276269182602),(2296101888,98276312553858,98276691873502)]
theorem point_links_checked17487 : (cuts17487.take 2).map (fun c => (2295988225-1+2*2^9*c.k,98275659142940+c.lower,98276038462190+c.upper)) = pointBounds17487 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000233
