import PlattAssemblyKernel
import PlattCertificates.Count131072.C071536
import PlattCertificates.Count131072.C071537
import PlattCertificates.Count131072.C071538
import PlattCertificates.Count131072.C071539
import PlattCertificates.Count131072.C071540
import PlattCertificates.Count131072.C071541
import PlattCertificates.Count131072.C071542
import PlattCertificates.Count131072.C071543
import PlattCertificates.Count131072.C071544
import PlattCertificates.Count131072.C071545
import PlattCertificates.Count131072.C071546
import PlattCertificates.Count131072.C071547
import PlattCertificates.Count131072.C071548
import PlattCertificates.Count131072.C071549
import PlattCertificates.Count131072.C071550
import PlattCertificates.Count131072.C071551
import PlattCertificates.Count131072.C071552
import PlattCertificates.Count131072.C071553
import PlattCertificates.Count131072.C071554
import PlattCertificates.Count131072.C071555
import PlattCertificates.Count131072.C071556
import PlattCertificates.Count131072.C071557
import PlattCertificates.Count131072.C071558
import PlattCertificates.Count131072.C071559
import PlattCertificates.Count131072.C071560
import PlattCertificates.Count131072.C071561
import PlattCertificates.Count131072.C071562
import PlattCertificates.Count131072.C071563
import PlattCertificates.Count131072.C071564
import PlattCertificates.Count131072.C071565
import PlattCertificates.Count131072.C071566
import PlattCertificates.Count131072.C071567
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000048
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts71536 : List PrefixCut := [⟨64,170288693,170288793⟩]
theorem checked71536 : checkPrefixCuts (2^48) 9380298753 10 Manual.Count131072.C071536.packed 64 cuts71536 = true := by
 decide +kernel
def cuts71537 : List PrefixCut := [⟨64,170886445,170886548⟩]
theorem checked71537 : checkPrefixCuts (2^48) 9380429825 10 Manual.Count131072.C071537.packed 64 cuts71537 = true := by
 decide +kernel
def cuts71538 : List PrefixCut := [⟨14,37897760,37897782⟩,
⟨64,172594397,172594499⟩]
theorem checked71538 : checkPrefixCuts (2^48) 9380560897 10 Manual.Count131072.C071538.packed 64 cuts71538 = true := by
 decide +kernel
def pointBounds71538 : List (Nat × Nat × Nat) := [(9380589568,116080213079498,116080602742016)]
theorem point_links_checked71538 : (cuts71538.take 1).map (fun c => (9380560897-1+2*2^10*c.k,116080175181738+c.lower,116080564844234+c.upper)) = pointBounds71538 := by
 decide +kernel
def cuts71539 : List PrefixCut := [⟨64,170101518,170101618⟩]
theorem checked71539 : checkPrefixCuts (2^48) 9380691969 10 Manual.Count131072.C071539.packed 64 cuts71539 = true := by
 decide +kernel
def cuts71540 : List PrefixCut := [⟨30,80084021,80084068⟩,
⟨64,169859112,169859212⟩]
theorem checked71540 : checkPrefixCuts (2^48) 9380823041 10 Manual.Count131072.C071540.packed 64 cuts71540 = true := by
 decide +kernel
def pointBounds71540 : List (Nat × Nat × Nat) := [(9380884480,116080597961674,116080987624419)]
theorem point_links_checked71540 : (cuts71540.take 1).map (fun c => (9380823041-1+2*2^10*c.k,116080517877653+c.lower,116080907540351+c.upper)) = pointBounds71540 := by
 decide +kernel
def cuts71541 : List PrefixCut := [⟨64,172437149,172437251⟩]
theorem checked71541 : checkPrefixCuts (2^48) 9380954113 10 Manual.Count131072.C071541.packed 64 cuts71541 = true := by
 decide +kernel
def cuts71542 : List PrefixCut := [⟨46,124698140,124698212⟩,
⟨64,171744652,171744751⟩]
theorem checked71542 : checkPrefixCuts (2^48) 9381085185 10 Manual.Count131072.C071542.packed 64 cuts71542 = true := by
 decide +kernel
def pointBounds71542 : List (Nat × Nat × Nat) := [(9381179392,116080984872054,116081374535026)]
theorem point_links_checked71542 : (cuts71542.take 1).map (fun c => (9381085185-1+2*2^10*c.k,116080860173914+c.lower,116081249836814+c.upper)) = pointBounds71542 := by
 decide +kernel
def cuts71543 : List PrefixCut := [⟨64,170092017,170092120⟩]
theorem checked71543 : checkPrefixCuts (2^48) 9381216257 10 Manual.Count131072.C071543.packed 64 cuts71543 = true := by
 decide +kernel
def cuts71544 : List PrefixCut := [⟨62,165229120,165229219⟩,
⟨64,170659710,170659813⟩]
theorem checked71544 : checkPrefixCuts (2^48) 9381347329 10 Manual.Count131072.C071544.packed 64 cuts71544 = true := by
 decide +kernel
def pointBounds71544 : List (Nat × Nat × Nat) := [(9381474304,116081367239703,116081756902904)]
theorem point_links_checked71544 : (cuts71544.take 1).map (fun c => (9381347329-1+2*2^10*c.k,116081202010583+c.lower,116081591673685+c.upper)) = pointBounds71544 := by
 decide +kernel
def cuts71545 : List PrefixCut := [⟨64,170147270,170147376⟩]
theorem checked71545 : checkPrefixCuts (2^48) 9381478401 10 Manual.Count131072.C071545.packed 64 cuts71545 = true := by
 decide +kernel
def cuts71546 : List PrefixCut := [⟨64,171344998,171345097⟩]
theorem checked71546 : checkPrefixCuts (2^48) 9381609473 10 Manual.Count131072.C071546.packed 64 cuts71546 = true := by
 decide +kernel
def cuts71547 : List PrefixCut := [⟨14,37052928,37052950⟩,
⟨64,171882655,171882753⟩]
theorem checked71547 : checkPrefixCuts (2^48) 9381740545 10 Manual.Count131072.C071547.packed 64 cuts71547 = true := by
 decide +kernel
def pointBounds71547 : List (Nat × Nat × Nat) := [(9381769216,116081751215489,116082140878921)]
theorem point_links_checked71547 : (cuts71547.take 1).map (fun c => (9381740545-1+2*2^10*c.k,116081714162561+c.lower,116082103825971+c.upper)) = pointBounds71547 := by
 decide +kernel
def cuts71548 : List PrefixCut := [⟨64,169600104,169600200⟩]
theorem checked71548 : checkPrefixCuts (2^48) 9381871617 10 Manual.Count131072.C071548.packed 64 cuts71548 = true := by
 decide +kernel
def cuts71549 : List PrefixCut := [⟨30,80463969,80464017⟩,
⟨64,170527786,170527888⟩]
theorem checked71549 : checkPrefixCuts (2^48) 9382002689 10 Manual.Count131072.C071549.packed 64 cuts71549 = true := by
 decide +kernel
def pointBounds71549 : List (Nat × Nat × Nat) := [(9382064128,116082136109289,116082525772941)]
theorem point_links_checked71549 : (cuts71549.take 1).map (fun c => (9382002689-1+2*2^10*c.k,116082055645320+c.lower,116082445308924+c.upper)) = pointBounds71549 := by
 decide +kernel
def cuts71550 : List PrefixCut := [⟨64,169745373,169745477⟩]
theorem checked71550 : checkPrefixCuts (2^48) 9382133761 10 Manual.Count131072.C071550.packed 64 cuts71550 = true := by
 decide +kernel
def cuts71551 : List PrefixCut := [⟨46,122132397,122132471⟩,
⟨64,170193008,170193108⟩]
theorem checked71551 : checkPrefixCuts (2^48) 9382264833 10 Manual.Count131072.C071551.packed 64 cuts71551 = true := by
 decide +kernel
def pointBounds71551 : List (Nat × Nat × Nat) := [(9382359040,116082518050876,116082907714760)]
theorem point_links_checked71551 : (cuts71551.take 1).map (fun c => (9382264833-1+2*2^10*c.k,116082395918479+c.lower,116082785582289+c.upper)) = pointBounds71551 := by
 decide +kernel
def cuts71552 : List PrefixCut := [⟨64,169800641,169800743⟩]
theorem checked71552 : checkPrefixCuts (2^48) 9382395905 10 Manual.Count131072.C071552.packed 64 cuts71552 = true := by
 decide +kernel
def cuts71553 : List PrefixCut := [⟨62,168148313,168148406⟩,
⟨64,172888232,172888328⟩]
theorem checked71553 : checkPrefixCuts (2^48) 9382526977 10 Manual.Count131072.C071553.packed 64 cuts71553 = true := by
 decide +kernel
def pointBounds71553 : List (Nat × Nat × Nat) := [(9382653952,116082904060441,116083293724546)]
theorem point_links_checked71553 : (cuts71553.take 1).map (fun c => (9382526977-1+2*2^10*c.k,116082735912128+c.lower,116083125576140+c.upper)) = pointBounds71553 := by
 decide +kernel
def cuts71554 : List PrefixCut := [⟨64,171835830,171835936⟩]
theorem checked71554 : checkPrefixCuts (2^48) 9382658049 10 Manual.Count131072.C071554.packed 64 cuts71554 = true := by
 decide +kernel
def cuts71555 : List PrefixCut := [⟨64,171473455,171473562⟩]
theorem checked71555 : checkPrefixCuts (2^48) 9382789121 10 Manual.Count131072.C071555.packed 64 cuts71555 = true := by
 decide +kernel
def cuts71556 : List PrefixCut := [⟨14,37918229,37918252⟩,
⟨64,171921026,171921128⟩]
theorem checked71556 : checkPrefixCuts (2^48) 9382920193 10 Manual.Count131072.C071556.packed 64 cuts71556 = true := by
 decide +kernel
def pointBounds71556 : List (Nat × Nat × Nat) := [(9382948864,116083290027874,116083679692218)]
theorem point_links_checked71556 : (cuts71556.take 1).map (fun c => (9382920193-1+2*2^10*c.k,116083252109645+c.lower,116083641773966+c.upper)) = pointBounds71556 := by
 decide +kernel
def cuts71557 : List PrefixCut := [⟨64,173988496,173988600⟩]
theorem checked71557 : checkPrefixCuts (2^48) 9383051265 10 Manual.Count131072.C071557.packed 64 cuts71557 = true := by
 decide +kernel
def cuts71558 : List PrefixCut := [⟨30,79163953,79164000⟩,
⟨64,170566333,170566430⟩]
theorem checked71558 : checkPrefixCuts (2^48) 9383182337 10 Manual.Count131072.C071558.packed 64 cuts71558 = true := by
 decide +kernel
def pointBounds71558 : List (Nat × Nat × Nat) := [(9383243776,116083677183120,116084066847694)]
theorem point_links_checked71558 : (cuts71558.take 1).map (fun c => (9383182337-1+2*2^10*c.k,116083598019167+c.lower,116083987683694+c.upper)) = pointBounds71558 := by
 decide +kernel
def cuts71559 : List PrefixCut := [⟨64,171613866,171613963⟩]
theorem checked71559 : checkPrefixCuts (2^48) 9383313409 10 Manual.Count131072.C071559.packed 64 cuts71559 = true := by
 decide +kernel
def cuts71560 : List PrefixCut := [⟨46,122327030,122327106⟩,
⟨64,170981528,170981633⟩]
theorem checked71560 : checkPrefixCuts (2^48) 9383444481 10 Manual.Count131072.C071560.packed 64 cuts71560 = true := by
 decide +kernel
def pointBounds71560 : List (Nat × Nat × Nat) := [(9383538688,116084062526396,116084452191193)]
theorem point_links_checked71560 : (cuts71560.take 1).map (fun c => (9383444481-1+2*2^10*c.k,116083940199366+c.lower,116084329864087+c.upper)) = pointBounds71560 := by
 decide +kernel
def cuts71561 : List PrefixCut := [⟨64,168279467,168279564⟩]
theorem checked71561 : checkPrefixCuts (2^48) 9383575553 10 Manual.Count131072.C071561.packed 64 cuts71561 = true := by
 decide +kernel
def cuts71562 : List PrefixCut := [⟨62,166807354,166807444⟩,
⟨64,172176588,172176680⟩]
theorem checked71562 : checkPrefixCuts (2^48) 9383706625 10 Manual.Count131072.C071562.packed 64 cuts71562 = true := by
 decide +kernel
def pointBounds71562 : List (Nat × Nat × Nat) := [(9383833600,116084446267715,116084835932728)]
theorem point_links_checked71562 : (cuts71562.take 1).map (fun c => (9383706625-1+2*2^10*c.k,116084279460361+c.lower,116084669125284+c.upper)) = pointBounds71562 := by
 decide +kernel
def cuts71563 : List PrefixCut := [⟨64,171664253,171664352⟩]
theorem checked71563 : checkPrefixCuts (2^48) 9383837697 10 Manual.Count131072.C071563.packed 64 cuts71563 = true := by
 decide +kernel
def cuts71564 : List PrefixCut := [⟨64,174271437,174271540⟩]
theorem checked71564 : checkPrefixCuts (2^48) 9383968769 10 Manual.Count131072.C071564.packed 64 cuts71564 = true := by
 decide +kernel
def cuts71565 : List PrefixCut := [⟨14,39083259,39083285⟩,
⟨64,173129207,173129314⟩]
theorem checked71565 : checkPrefixCuts (2^48) 9384099841 10 Manual.Count131072.C071565.packed 64 cuts71565 = true := by
 decide +kernel
def pointBounds71565 : List (Nat × Nat × Nat) := [(9384128512,116084836655898,116085226321141)]
theorem point_links_checked71565 : (cuts71565.take 1).map (fun c => (9384099841-1+2*2^10*c.k,116084797572639+c.lower,116085187237856+c.upper)) = pointBounds71565 := by
 decide +kernel
def cuts71566 : List PrefixCut := [⟨64,173636681,173636782⟩]
theorem checked71566 : checkPrefixCuts (2^48) 9384230913 10 Manual.Count131072.C071566.packed 64 cuts71566 = true := by
 decide +kernel
def cuts71567 : List PrefixCut := [⟨30,78704097,78704143⟩,
⟨64,168685284,168685381⟩]
theorem checked71567 : checkPrefixCuts (2^48) 9384361985 10 Manual.Count131072.C071567.packed 64 cuts71567 = true := by
 decide +kernel
def pointBounds71567 : List (Nat × Nat × Nat) := [(9384423424,116085223042624,116085612708095)]
theorem point_links_checked71567 : (cuts71567.take 1).map (fun c => (9384361985-1+2*2^10*c.k,116085144338527+c.lower,116085534003952+c.upper)) = pointBounds71567 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000048
