import PlattAssemblyKernel
import PlattCertificates.Count131072.C075280
import PlattCertificates.Count131072.C075281
import PlattCertificates.Count131072.C075282
import PlattCertificates.Count131072.C075283
import PlattCertificates.Count131072.C075284
import PlattCertificates.Count131072.C075285
import PlattCertificates.Count131072.C075286
import PlattCertificates.Count131072.C075287
import PlattCertificates.Count131072.C075288
import PlattCertificates.Count131072.C075289
import PlattCertificates.Count131072.C075290
import PlattCertificates.Count131072.C075291
import PlattCertificates.Count131072.C075292
import PlattCertificates.Count131072.C075293
import PlattCertificates.Count131072.C075294
import PlattCertificates.Count131072.C075295
import PlattCertificates.Count131072.C075296
import PlattCertificates.Count131072.C075297
import PlattCertificates.Count131072.C075298
import PlattCertificates.Count131072.C075299
import PlattCertificates.Count131072.C075300
import PlattCertificates.Count131072.C075301
import PlattCertificates.Count131072.C075302
import PlattCertificates.Count131072.C075303
import PlattCertificates.Count131072.C075304
import PlattCertificates.Count131072.C075305
import PlattCertificates.Count131072.C075306
import PlattCertificates.Count131072.C075307
import PlattCertificates.Count131072.C075308
import PlattCertificates.Count131072.C075309
import PlattCertificates.Count131072.C075310
import PlattCertificates.Count131072.C075311
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75280 : List PrefixCut := [⟨64,160454206,160454307⟩]
theorem checked75280 : checkPrefixCuts (2^48) 9871032321 10 Manual.Count131072.C075280.packed 64 cuts75280 = true := by
 decide +kernel
def cuts75281 : List PrefixCut := [⟨59,147021742,147021827⟩,
⟨64,159539608,159539702⟩]
theorem checked75281 : checkPrefixCuts (2^48) 9871163393 10 Manual.Count131072.C075281.packed 64 cuts75281 = true := by
 decide +kernel
def pointBounds75281 : List (Nat × Nat × Nat) := [(9871284224,116704585365678,116704975400524)]
theorem point_links_checked75281 : (cuts75281.take 1).map (fun c => (9871163393-1+2*2^10*c.k,116704438343936+c.lower,116704828378697+c.upper)) = pointBounds75281 := by
 decide +kernel
def cuts75282 : List PrefixCut := [⟨64,163073264,163073358⟩]
theorem checked75282 : checkPrefixCuts (2^48) 9871294465 10 Manual.Count131072.C075282.packed 64 cuts75282 = true := by
 decide +kernel
def cuts75283 : List PrefixCut := [⟨64,163983548,163983639⟩]
theorem checked75283 : checkPrefixCuts (2^48) 9871425537 10 Manual.Count131072.C075283.packed 64 cuts75283 = true := by
 decide +kernel
def cuts75284 : List PrefixCut := [⟨18,45907021,45907046⟩,
⟨64,162498671,162498767⟩]
theorem checked75284 : checkPrefixCuts (2^48) 9871556609 10 Manual.Count131072.C075284.packed 64 cuts75284 = true := by
 decide +kernel
def pointBounds75284 : List (Nat × Nat × Nat) := [(9871593472,116704970847377,116705360882442)]
theorem point_links_checked75284 : (cuts75284.take 1).map (fun c => (9871556609-1+2*2^10*c.k,116704924940356+c.lower,116705314975396+c.upper)) = pointBounds75284 := by
 decide +kernel
def cuts75285 : List PrefixCut := [⟨64,163580006,163580104⟩]
theorem checked75285 : checkPrefixCuts (2^48) 9871687681 10 Manual.Count131072.C075285.packed 64 cuts75285 = true := by
 decide +kernel
def cuts75286 : List PrefixCut := [⟨41,105240936,105240999⟩,
⟨64,163606350,163606453⟩]
theorem checked75286 : checkPrefixCuts (2^48) 9871818753 10 Manual.Count131072.C075286.packed 64 cuts75286 = true := by
 decide +kernel
def pointBounds75286 : List (Nat × Nat × Nat) := [(9871902720,116705356259969,116705746295266)]
theorem point_links_checked75286 : (cuts75286.take 1).map (fun c => (9871818753-1+2*2^10*c.k,116705251019033+c.lower,116705641054267+c.upper)) = pointBounds75286 := by
 decide +kernel
def cuts75287 : List PrefixCut := [⟨64,166084748,166084853⟩]
theorem checked75287 : checkPrefixCuts (2^48) 9871949825 10 Manual.Count131072.C075287.packed 64 cuts75287 = true := by
 decide +kernel
def cuts75288 : List PrefixCut := [⟨64,164457353,164457448⟩]
theorem checked75288 : checkPrefixCuts (2^48) 9872080897 10 Manual.Count131072.C075288.packed 64 cuts75288 = true := by
 decide +kernel
def pointBounds75288 : List (Nat × Nat × Nat) := [(9872211968,116705745167484,116706135203021)]
theorem point_links_checked75288 : (cuts75288.take 1).map (fun c => (9872080897-1+2*2^10*c.k,116705580710131+c.lower,116705970745573+c.upper)) = pointBounds75288 := by
 decide +kernel
def cuts75289 : List PrefixCut := [⟨64,163713879,163713980⟩]
theorem checked75289 : checkPrefixCuts (2^48) 9872211969 10 Manual.Count131072.C075289.packed 64 cuts75289 = true := by
 decide +kernel
def cuts75290 : List PrefixCut := [⟨64,162428690,162428793⟩]
theorem checked75290 : checkPrefixCuts (2^48) 9872343041 10 Manual.Count131072.C075290.packed 64 cuts75290 = true := by
 decide +kernel
def cuts75291 : List PrefixCut := [⟨23,58390549,58390586⟩,
⟨64,161229084,161229188⟩]
theorem checked75291 : checkPrefixCuts (2^48) 9872474113 10 Manual.Count131072.C075291.packed 64 cuts75291 = true := by
 decide +kernel
def pointBounds75291 : List (Nat × Nat × Nat) := [(9872521216,116706129700602,116706519736380)]
theorem point_links_checked75291 : (cuts75291.take 1).map (fun c => (9872474113-1+2*2^10*c.k,116706071310053+c.lower,116706461345794+c.upper)) = pointBounds75291 := by
 decide +kernel
def cuts75292 : List PrefixCut := [⟨64,162338852,162338949⟩]
theorem checked75292 : checkPrefixCuts (2^48) 9872605185 10 Manual.Count131072.C075292.packed 64 cuts75292 = true := by
 decide +kernel
def cuts75293 : List PrefixCut := [⟨46,117461969,117462038⟩,
⟨64,161652463,161652562⟩]
theorem checked75293 : checkPrefixCuts (2^48) 9872736257 10 Manual.Count131072.C075293.packed 64 cuts75293 = true := by
 decide +kernel
def pointBounds75293 : List (Nat × Nat × Nat) := [(9872830464,116706512339958,116706902375969)]
theorem point_links_checked75293 : (cuts75293.take 1).map (fun c => (9872736257-1+2*2^10*c.k,116706394877989+c.lower,116706784913931+c.upper)) = pointBounds75293 := by
 decide +kernel
def cuts75294 : List PrefixCut := [⟨64,163645986,163646082⟩]
theorem checked75294 : checkPrefixCuts (2^48) 9872867329 10 Manual.Count131072.C075294.packed 64 cuts75294 = true := by
 decide +kernel
def cuts75295 : List PrefixCut := [⟨64,159395919,159396014⟩]
theorem checked75295 : checkPrefixCuts (2^48) 9872998401 10 Manual.Count131072.C075295.packed 64 cuts75295 = true := by
 decide +kernel
def cuts75296 : List PrefixCut := [⟨5,12601054,12601061⟩,
⟨64,163413574,163413673⟩]
theorem checked75296 : checkPrefixCuts (2^48) 9873129473 10 Manual.Count131072.C075296.packed 64 cuts75296 = true := by
 decide +kernel
def pointBounds75296 : List (Nat × Nat × Nat) := [(9873139712,116706892173411,116707282209650)]
theorem point_links_checked75296 : (cuts75296.take 1).map (fun c => (9873129473-1+2*2^10*c.k,116706879572357+c.lower,116707269608589+c.upper)) = pointBounds75296 := by
 decide +kernel
def cuts75297 : List PrefixCut := [⟨64,162014483,162014581⟩]
theorem checked75297 : checkPrefixCuts (2^48) 9873260545 10 Manual.Count131072.C075297.packed 64 cuts75297 = true := by
 decide +kernel
def cuts75298 : List PrefixCut := [⟨28,71213855,71213895⟩,
⟨64,161755761,161755854⟩]
theorem checked75298 : checkPrefixCuts (2^48) 9873391617 10 Manual.Count131072.C075298.packed 64 cuts75298 = true := by
 decide +kernel
def pointBounds75298 : List (Nat × Nat × Nat) := [(9873448960,116707276214269,116707666250738)]
theorem point_links_checked75298 : (cuts75298.take 1).map (fun c => (9873391617-1+2*2^10*c.k,116707205000414+c.lower,116707595036843+c.upper)) = pointBounds75298 := by
 decide +kernel
def cuts75299 : List PrefixCut := [⟨64,164119757,164119852⟩]
theorem checked75299 : checkPrefixCuts (2^48) 9873522689 10 Manual.Count131072.C075299.packed 64 cuts75299 = true := by
 decide +kernel
def cuts75300 : List PrefixCut := [⟨51,129766242,129766320⟩,
⟨64,163319372,163319469⟩]
theorem checked75300 : checkPrefixCuts (2^48) 9873653761 10 Manual.Count131072.C075300.packed 64 cuts75300 = true := by
 decide +kernel
def pointBounds75300 : List (Nat × Nat × Nat) := [(9873758208,116707660642174,116708050678869)]
theorem point_links_checked75300 : (cuts75300.take 1).map (fun c => (9873653761-1+2*2^10*c.k,116707530875932+c.lower,116707920912549+c.upper)) = pointBounds75300 := by
 decide +kernel
def cuts75301 : List PrefixCut := [⟨64,162946613,162946707⟩]
theorem checked75301 : checkPrefixCuts (2^48) 9873784833 10 Manual.Count131072.C075301.packed 64 cuts75301 = true := by
 decide +kernel
def cuts75302 : List PrefixCut := [⟨64,164341294,164341392⟩]
theorem checked75302 : checkPrefixCuts (2^48) 9873915905 10 Manual.Count131072.C075302.packed 64 cuts75302 = true := by
 decide +kernel
def cuts75303 : List PrefixCut := [⟨10,25427805,25427820⟩,
⟨64,162514689,162514787⟩]
theorem checked75303 : checkPrefixCuts (2^48) 9874046977 10 Manual.Count131072.C075303.packed 64 cuts75303 = true := by
 decide +kernel
def pointBounds75303 : List (Nat × Nat × Nat) := [(9874067456,116708046911016,116708436947937)]
theorem point_links_checked75303 : (cuts75303.take 1).map (fun c => (9874046977-1+2*2^10*c.k,116708021483211+c.lower,116708411520117+c.upper)) = pointBounds75303 := by
 decide +kernel
def cuts75304 : List PrefixCut := [⟨64,161429319,161429409⟩]
theorem checked75304 : checkPrefixCuts (2^48) 9874178049 10 Manual.Count131072.C075304.packed 64 cuts75304 = true := by
 decide +kernel
def cuts75305 : List PrefixCut := [⟨33,84490852,84490896⟩,
⟨64,164819334,164819428⟩]
theorem checked75305 : checkPrefixCuts (2^48) 9874309121 10 Manual.Count131072.C075305.packed 64 cuts75305 = true := by
 decide +kernel
def pointBounds75305 : List (Nat × Nat × Nat) := [(9874376704,116708429918071,116708819955209)]
theorem point_links_checked75305 : (cuts75305.take 1).map (fun c => (9874309121-1+2*2^10*c.k,116708345427219+c.lower,116708735464313+c.upper)) = pointBounds75305 := by
 decide +kernel
def cuts75306 : List PrefixCut := [⟨64,161938117,161938216⟩]
theorem checked75306 : checkPrefixCuts (2^48) 9874440193 10 Manual.Count131072.C075306.packed 64 cuts75306 = true := by
 decide +kernel
def cuts75307 : List PrefixCut := [⟨56,138932680,138932768⟩,
⟨64,159113987,159114087⟩]
theorem checked75307 : checkPrefixCuts (2^48) 9874571265 10 Manual.Count131072.C075307.packed 64 cuts75307 = true := by
 decide +kernel
def pointBounds75307 : List (Nat × Nat × Nat) := [(9874685952,116708811117350,116709201154725)]
theorem point_links_checked75307 : (cuts75307.take 1).map (fun c => (9874571265-1+2*2^10*c.k,116708672184670+c.lower,116709062221957+c.upper)) = pointBounds75307 := by
 decide +kernel
def cuts75308 : List PrefixCut := [⟨64,161990829,161990916⟩]
theorem checked75308 : checkPrefixCuts (2^48) 9874702337 10 Manual.Count131072.C075308.packed 64 cuts75308 = true := by
 decide +kernel
def cuts75309 : List PrefixCut := [⟨64,164297512,164297604⟩]
theorem checked75309 : checkPrefixCuts (2^48) 9874833409 10 Manual.Count131072.C075309.packed 64 cuts75309 = true := by
 decide +kernel
def cuts75310 : List PrefixCut := [⟨15,37568066,37568091⟩,
⟨64,162015034,162015126⟩]
theorem checked75310 : checkPrefixCuts (2^48) 9874964481 10 Manual.Count131072.C075310.packed 64 cuts75310 = true := by
 decide +kernel
def pointBounds75310 : List (Nat × Nat × Nat) := [(9874995200,116709195155064,116709585192655)]
theorem point_links_checked75310 : (cuts75310.take 1).map (fun c => (9874964481-1+2*2^10*c.k,116709157586998+c.lower,116709547624564+c.upper)) = pointBounds75310 := by
 decide +kernel
def cuts75311 : List PrefixCut := [⟨64,161699343,161699441⟩]
theorem checked75311 : checkPrefixCuts (2^48) 9875095553 10 Manual.Count131072.C075311.packed 64 cuts75311 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000165
