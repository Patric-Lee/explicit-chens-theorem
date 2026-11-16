import PlattAssemblyKernel
import PlattCertificates.Count131072.C040544
import PlattCertificates.Count131072.C040545
import PlattCertificates.Count131072.C040546
import PlattCertificates.Count131072.C040547
import PlattCertificates.Count131072.C040548
import PlattCertificates.Count131072.C040549
import PlattCertificates.Count131072.C040550
import PlattCertificates.Count131072.C040551
import PlattCertificates.Count131072.C040552
import PlattCertificates.Count131072.C040553
import PlattCertificates.Count131072.C040554
import PlattCertificates.Count131072.C040555
import PlattCertificates.Count131072.C040556
import PlattCertificates.Count131072.C040557
import PlattCertificates.Count131072.C040558
import PlattCertificates.Count131072.C040559
import PlattCertificates.Count131072.C040560
import PlattCertificates.Count131072.C040561
import PlattCertificates.Count131072.C040562
import PlattCertificates.Count131072.C040563
import PlattCertificates.Count131072.C040564
import PlattCertificates.Count131072.C040565
import PlattCertificates.Count131072.C040566
import PlattCertificates.Count131072.C040567
import PlattCertificates.Count131072.C040568
import PlattCertificates.Count131072.C040569
import PlattCertificates.Count131072.C040570
import PlattCertificates.Count131072.C040571
import PlattCertificates.Count131072.C040572
import PlattCertificates.Count131072.C040573
import PlattCertificates.Count131072.C040574
import PlattCertificates.Count131072.C040575
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000017
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40544 : List PrefixCut := [⟨17,84842604,84842655⟩,
⟨64,311739525,311739713⟩]
theorem checked40544 : checkPrefixCuts (2^48) 5318115329 10 Manual.Count131072.C040544.packed 64 cuts40544 = true := by
 decide +kernel
def pointBounds40544 : List (Nat × Nat × Nat) := [(5318150144,109036028126384,109036413732743)]
theorem point_links_checked40544 : (cuts40544.take 1).map (fun c => (5318115329-1+2*2^10*c.k,109035943283780+c.lower,109036328890088+c.upper)) = pointBounds40544 := by
 decide +kernel
def cuts40545 : List PrefixCut := [⟨35,165181737,165181837⟩,
⟨64,308662105,308662289⟩]
theorem checked40545 : checkPrefixCuts (2^48) 5318246401 10 Manual.Count131072.C040545.packed 64 cuts40545 = true := by
 decide +kernel
def pointBounds40545 : List (Nat × Nat × Nat) := [(5318318080,109036420205042,109036805811638)]
theorem point_links_checked40545 : (cuts40545.take 1).map (fun c => (5318246401-1+2*2^10*c.k,109036255023305+c.lower,109036640629801+c.upper)) = pointBounds40545 := by
 decide +kernel
def cuts40546 : List PrefixCut := [⟨53,257583141,257583296⟩,
⟨64,311353686,311353875⟩]
theorem checked40546 : checkPrefixCuts (2^48) 5318377473 10 Manual.Count131072.C040546.packed 64 cuts40546 = true := by
 decide +kernel
def pointBounds40546 : List (Nat × Nat × Nat) := [(5318486016,109036821268551,109037206875386)]
theorem point_links_checked40546 : (cuts40546.take 1).map (fun c => (5318377473-1+2*2^10*c.k,109036563685410+c.lower,109036949292090+c.upper)) = pointBounds40546 := by
 decide +kernel
def cuts40547 : List PrefixCut := [⟨64,312139822,312140002⟩]
theorem checked40547 : checkPrefixCuts (2^48) 5318508545 10 Manual.Count131072.C040547.packed 64 cuts40547 = true := by
 decide +kernel
def cuts40548 : List PrefixCut := [⟨7,33446877,33446898⟩,
⟨64,306998735,306998919⟩]
theorem checked40548 : checkPrefixCuts (2^48) 5318639617 10 Manual.Count131072.C040548.packed 64 cuts40548 = true := by
 decide +kernel
def pointBounds40548 : List (Nat × Nat × Nat) := [(5318653952,109037220625795,109037606232865)]
theorem point_links_checked40548 : (cuts40548.take 1).map (fun c => (5318639617-1+2*2^10*c.k,109037187178918+c.lower,109037572785967+c.upper)) = pointBounds40548 := by
 decide +kernel
def cuts40549 : List PrefixCut := [⟨25,120077264,120077335⟩,
⟨64,308049584,308049765⟩]
theorem checked40549 : checkPrefixCuts (2^48) 5318770689 10 Manual.Count131072.C040549.packed 64 cuts40549 = true := by
 decide +kernel
def pointBounds40549 : List (Nat × Nat × Nat) := [(5318821888,109037614254917,109037999862221)]
theorem point_links_checked40549 : (cuts40549.take 1).map (fun c => (5318770689-1+2*2^10*c.k,109037494177653+c.lower,109037879784886+c.upper)) = pointBounds40549 := by
 decide +kernel
def cuts40550 : List PrefixCut := [⟨43,205591479,205591603⟩,
⟨64,306083992,306084176⟩]
theorem checked40550 : checkPrefixCuts (2^48) 5318901761 10 Manual.Count131072.C040550.packed 64 cuts40550 = true := by
 decide +kernel
def pointBounds40550 : List (Nat × Nat × Nat) := [(5318989824,109038007818716,109038393426254)]
theorem point_links_checked40550 : (cuts40550.take 1).map (fun c => (5318901761-1+2*2^10*c.k,109037802227237+c.lower,109038187834651+c.upper)) = pointBounds40550 := by
 decide +kernel
def cuts40551 : List PrefixCut := [⟨61,296868920,296869097⟩,
⟨64,311579892,311580078⟩]
theorem checked40551 : checkPrefixCuts (2^48) 5319032833 10 Manual.Count131072.C040551.packed 64 cuts40551 = true := by
 decide +kernel
def pointBounds40551 : List (Nat × Nat × Nat) := [(5319157760,109038405180149,109038790787924)]
theorem point_links_checked40551 : (cuts40551.take 1).map (fun c => (5319032833-1+2*2^10*c.k,109038108311229+c.lower,109038493918827+c.upper)) = pointBounds40551 := by
 decide +kernel
def cuts40552 : List PrefixCut := [⟨64,313265576,313265763⟩]
theorem checked40552 : checkPrefixCuts (2^48) 5319163905 10 Manual.Count131072.C040552.packed 64 cuts40552 = true := by
 decide +kernel
def cuts40553 : List PrefixCut := [⟨15,73235291,73235336⟩,
⟨64,309659614,309659796⟩]
theorem checked40553 : checkPrefixCuts (2^48) 5319294977 10 Manual.Count131072.C040553.packed 64 cuts40553 = true := by
 decide +kernel
def pointBounds40553 : List (Nat × Nat × Nat) := [(5319325696,109038806391988,109039192000004)]
theorem point_links_checked40553 : (cuts40553.take 1).map (fun c => (5319294977-1+2*2^10*c.k,109038733156697+c.lower,109039118764668+c.upper)) = pointBounds40553 := by
 decide +kernel
def cuts40554 : List PrefixCut := [⟨33,161388262,161388357⟩,
⟨64,308964116,308964300⟩]
theorem checked40554 : checkPrefixCuts (2^48) 5319426049 10 Manual.Count131072.C040554.packed 64 cuts40554 = true := by
 decide +kernel
def pointBounds40554 : List (Nat × Nat × Nat) := [(5319493632,109039204204573,109039589812821)]
theorem point_links_checked40554 : (cuts40554.take 1).map (fun c => (5319426049-1+2*2^10*c.k,109039042816311+c.lower,109039428424464+c.upper)) = pointBounds40554 := by
 decide +kernel
def cuts40555 : List PrefixCut := [⟨51,246414445,246414593⟩,
⟨64,310914232,310914419⟩]
theorem checked40555 : checkPrefixCuts (2^48) 5319557121 10 Manual.Count131072.C040555.packed 64 cuts40555 = true := by
 decide +kernel
def pointBounds40555 : List (Nat × Nat × Nat) := [(5319661568,109039598194872,109039983803357)]
theorem point_links_checked40555 : (cuts40555.take 1).map (fun c => (5319557121-1+2*2^10*c.k,109039351780427+c.lower,109039737388764+c.upper)) = pointBounds40555 := by
 decide +kernel
def cuts40556 : List PrefixCut := [⟨64,312546829,312547014⟩]
theorem checked40556 : checkPrefixCuts (2^48) 5319688193 10 Manual.Count131072.C040556.packed 64 cuts40556 = true := by
 decide +kernel
def cuts40557 : List PrefixCut := [⟨5,23121917,23121930⟩,
⟨64,310475630,310475811⟩]
theorem checked40557 : checkPrefixCuts (2^48) 5319819265 10 Manual.Count131072.C040557.packed 64 cuts40557 = true := by
 decide +kernel
def pointBounds40557 : List (Nat × Nat × Nat) := [(5319829504,109039998363405,109040383972127)]
theorem point_links_checked40557 : (cuts40557.take 1).map (fun c => (5319819265-1+2*2^10*c.k,109039975241488+c.lower,109040360850197+c.upper)) = pointBounds40557 := by
 decide +kernel
def cuts40558 : List PrefixCut := [⟨23,109098505,109098570⟩,
⟨64,305441672,305441852⟩]
theorem checked40558 : checkPrefixCuts (2^48) 5319950337 10 Manual.Count131072.C040558.packed 64 cuts40558 = true := by
 decide +kernel
def pointBounds40558 : List (Nat × Nat × Nat) := [(5319997440,109040394815623,109040780424578)]
theorem point_links_checked40558 : (cuts40558.take 1).map (fun c => (5319950337-1+2*2^10*c.k,109040285717118+c.lower,109040671326008+c.upper)) = pointBounds40558 := by
 decide +kernel
def cuts40559 : List PrefixCut := [⟨41,199197078,199197190⟩,
⟨64,309984190,309984367⟩]
theorem checked40559 : checkPrefixCuts (2^48) 5320081409 10 Manual.Count131072.C040559.packed 64 cuts40559 = true := by
 decide +kernel
def pointBounds40559 : List (Nat × Nat × Nat) := [(5320165376,109040790355868,109041175965050)]
theorem point_links_checked40559 : (cuts40559.take 1).map (fun c => (5320081409-1+2*2^10*c.k,109040591158790+c.lower,109040976767860+c.upper)) = pointBounds40559 := by
 decide +kernel
def cuts40560 : List PrefixCut := [⟨59,281883699,281883865⟩,
⟨64,307437031,307437212⟩]
theorem checked40560 : checkPrefixCuts (2^48) 5320212481 10 Manual.Count131072.C040560.packed 64 cuts40560 = true := by
 decide +kernel
def pointBounds40560 : List (Nat × Nat × Nat) := [(5320333312,109041183026679,109041568636092)]
theorem point_links_checked40560 : (cuts40560.take 1).map (fun c => (5320212481-1+2*2^10*c.k,109040901142980+c.lower,109041286752227+c.upper)) = pointBounds40560 := by
 decide +kernel
def cuts40561 : List PrefixCut := [⟨64,307746916,307747099⟩]
theorem checked40561 : checkPrefixCuts (2^48) 5320343553 10 Manual.Count131072.C040561.packed 64 cuts40561 = true := by
 decide +kernel
def cuts40562 : List PrefixCut := [⟨13,63273140,63273177⟩,
⟨64,310596130,310596315⟩]
theorem checked40562 : checkPrefixCuts (2^48) 5320474625 10 Manual.Count131072.C040562.packed 64 cuts40562 = true := by
 decide +kernel
def pointBounds40562 : List (Nat × Nat × Nat) := [(5320501248,109041579600067,109041965209715)]
theorem point_links_checked40562 : (cuts40562.take 1).map (fun c => (5320474625-1+2*2^10*c.k,109041516326927+c.lower,109041901936538+c.upper)) = pointBounds40562 := by
 decide +kernel
def cuts40563 : List PrefixCut := [⟨31,149343692,149343781⟩,
⟨64,307044022,307044207⟩]
theorem checked40563 : checkPrefixCuts (2^48) 5320605697 10 Manual.Count131072.C040563.packed 64 cuts40563 = true := by
 decide +kernel
def pointBounds40563 : List (Nat × Nat × Nat) := [(5320669184,109041976266749,109042361876634)]
theorem point_links_checked40563 : (cuts40563.take 1).map (fun c => (5320605697-1+2*2^10*c.k,109041826923057+c.lower,109042212532853+c.upper)) = pointBounds40563 := by
 decide +kernel
def cuts40564 : List PrefixCut := [⟨49,242868440,242868583⟩,
⟨64,316188310,316188496⟩]
theorem checked40564 : checkPrefixCuts (2^48) 5320736769 10 Manual.Count131072.C040564.packed 64 cuts40564 = true := by
 decide +kernel
def pointBounds40564 : List (Nat × Nat × Nat) := [(5320837120,109042376835519,109042762445643)]
theorem point_links_checked40564 : (cuts40564.take 1).map (fun c => (5320736769-1+2*2^10*c.k,109042133967079+c.lower,109042519577060+c.upper)) = pointBounds40564 := by
 decide +kernel
def cuts40565 : List PrefixCut := [⟨64,310202841,310203023⟩]
theorem checked40565 : checkPrefixCuts (2^48) 5320867841 10 Manual.Count131072.C040565.packed 64 cuts40565 = true := by
 decide +kernel
def cuts40566 : List PrefixCut := [⟨3,13965297,13965304⟩,
⟨64,305540198,305540381⟩]
theorem checked40566 : checkPrefixCuts (2^48) 5320998913 10 Manual.Count131072.C040566.packed 64 cuts40566 = true := by
 decide +kernel
def pointBounds40566 : List (Nat × Nat × Nat) := [(5321005056,109042774323527,109043159933883)]
theorem point_links_checked40566 : (cuts40566.take 1).map (fun c => (5320998913-1+2*2^10*c.k,109042760358230+c.lower,109043145968579+c.upper)) = pointBounds40566 := by
 decide +kernel
def cuts40567 : List PrefixCut := [⟨21,102462190,102462250⟩,
⟨64,311457121,311457302⟩]
theorem checked40567 : checkPrefixCuts (2^48) 5321129985 10 Manual.Count131072.C040567.packed 64 cuts40567 = true := by
 decide +kernel
def pointBounds40567 : List (Nat × Nat × Nat) := [(5321172992,109043168360618,109043553971210)]
theorem point_links_checked40567 : (cuts40567.take 1).map (fun c => (5321129985-1+2*2^10*c.k,109043065898428+c.lower,109043451508960+c.upper)) = pointBounds40567 := by
 decide +kernel
def cuts40568 : List PrefixCut := [⟨39,187886159,187886270⟩,
⟨64,305683826,305684006⟩]
theorem checked40568 : checkPrefixCuts (2^48) 5321261057 10 Manual.Count131072.C040568.packed 64 cuts40568 = true := by
 decide +kernel
def pointBounds40568 : List (Nat × Nat × Nat) := [(5321340928,109043565241708,109043950852532)]
theorem point_links_checked40568 : (cuts40568.take 1).map (fun c => (5321261057-1+2*2^10*c.k,109043377355549+c.lower,109043762966262+c.upper)) = pointBounds40568 := by
 decide +kernel
def cuts40569 : List PrefixCut := [⟨57,277801370,277801531⟩,
⟨64,310436810,310436991⟩]
theorem checked40569 : checkPrefixCuts (2^48) 5321392129 10 Manual.Count131072.C040569.packed 64 cuts40569 = true := by
 decide +kernel
def pointBounds40569 : List (Nat × Nat × Nat) := [(5321508864,109043960840745,109044346451799)]
theorem point_links_checked40569 : (cuts40569.take 1).map (fun c => (5321392129-1+2*2^10*c.k,109043683039375+c.lower,109044068650268+c.upper)) = pointBounds40569 := by
 decide +kernel
def cuts40570 : List PrefixCut := [⟨64,309900203,309900386⟩]
theorem checked40570 : checkPrefixCuts (2^48) 5321523201 10 Manual.Count131072.C040570.packed 64 cuts40570 = true := by
 decide +kernel
def cuts40571 : List PrefixCut := [⟨11,54161668,54161701⟩,
⟨64,308252936,308253118⟩]
theorem checked40571 : checkPrefixCuts (2^48) 5321654273 10 Manual.Count131072.C040571.packed 64 cuts40571 = true := by
 decide +kernel
def pointBounds40571 : List (Nat × Nat × Nat) := [(5321676800,109044357538056,109044743149346)]
theorem point_links_checked40571 : (cuts40571.take 1).map (fun c => (5321654273-1+2*2^10*c.k,109044303376388+c.lower,109044688987645+c.upper)) = pointBounds40571 := by
 decide +kernel
def cuts40572 : List PrefixCut := [⟨29,142064610,142064693⟩,
⟨64,311947665,311947850⟩]
theorem checked40572 : checkPrefixCuts (2^48) 5321785345 10 Manual.Count131072.C040572.packed 64 cuts40572 = true := by
 decide +kernel
def pointBounds40572 : List (Nat × Nat × Nat) := [(5321844736,109044753693934,109045139305456)]
theorem point_links_checked40572 : (cuts40572.take 1).map (fun c => (5321785345-1+2*2^10*c.k,109044611629324+c.lower,109044997240763+c.upper)) = pointBounds40572 := by
 decide +kernel
def cuts40573 : List PrefixCut := [⟨47,224991025,224991160⟩,
⟨64,308131955,308132140⟩]
theorem checked40573 : checkPrefixCuts (2^48) 5321916417 10 Manual.Count131072.C040573.packed 64 cuts40573 = true := by
 decide +kernel
def pointBounds40573 : List (Nat × Nat × Nat) := [(5322012672,109045148568014,109045534179773)]
theorem point_links_checked40573 : (cuts40573.take 1).map (fun c => (5321916417-1+2*2^10*c.k,109044923576989+c.lower,109045309188613+c.upper)) = pointBounds40573 := by
 decide +kernel
def cuts40574 : List PrefixCut := [⟨64,311773662,311773850⟩]
theorem checked40574 : checkPrefixCuts (2^48) 5322047489 10 Manual.Count131072.C040574.packed 64 cuts40574 = true := by
 decide +kernel
def cuts40575 : List PrefixCut := [⟨1,4283859,4283861⟩,
⟨64,307217707,307217883⟩]
theorem checked40575 : checkPrefixCuts (2^48) 5322178561 10 Manual.Count131072.C040575.packed 64 cuts40575 = true := by
 decide +kernel
def pointBounds40575 : List (Nat × Nat × Nat) := [(5322180608,109045547766465,109045933378464)]
theorem point_links_checked40575 : (cuts40575.take 1).map (fun c => (5322178561-1+2*2^10*c.k,109045543482606+c.lower,109045929094603+c.upper)) = pointBounds40575 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000017
