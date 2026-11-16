import PlattAssemblyKernel
import PlattCertificates.Count131072.C064096
import PlattCertificates.Count131072.C064097
import PlattCertificates.Count131072.C064098
import PlattCertificates.Count131072.C064099
import PlattCertificates.Count131072.C064100
import PlattCertificates.Count131072.C064101
import PlattCertificates.Count131072.C064102
import PlattCertificates.Count131072.C064103
import PlattCertificates.Count131072.C064104
import PlattCertificates.Count131072.C064105
import PlattCertificates.Count131072.C064106
import PlattCertificates.Count131072.C064107
import PlattCertificates.Count131072.C064108
import PlattCertificates.Count131072.C064109
import PlattCertificates.Count131072.C064110
import PlattCertificates.Count131072.C064111
import PlattCertificates.Count131072.C064112
import PlattCertificates.Count131072.C064113
import PlattCertificates.Count131072.C064114
import PlattCertificates.Count131072.C064115
import PlattCertificates.Count131072.C064116
import PlattCertificates.Count131072.C064117
import PlattCertificates.Count131072.C064118
import PlattCertificates.Count131072.C064119
import PlattCertificates.Count131072.C064120
import PlattCertificates.Count131072.C064121
import PlattCertificates.Count131072.C064122
import PlattCertificates.Count131072.C064123
import PlattCertificates.Count131072.C064124
import PlattCertificates.Count131072.C064125
import PlattCertificates.Count131072.C064126
import PlattCertificates.Count131072.C064127
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000128
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts64096 : List PrefixCut := [⟨64,187567574,187567680⟩]
theorem checked64096 : checkPrefixCuts (2^48) 8405123073 10 Manual.Count131072.C064096.packed 64 cuts64096 = true := by
 decide +kernel
def cuts64097 : List PrefixCut := [⟨47,139844971,139845054⟩,
⟨64,190042758,190042871⟩]
theorem checked64097 : checkPrefixCuts (2^48) 8405254145 10 Manual.Count131072.C064097.packed 64 cuts64097 = true := by
 decide +kernel
def pointBounds64097 : List (Nat × Nat × Nat) := [(8405350400,114731375125701,114731764000395)]
theorem point_links_checked64097 : (cuts64097.take 1).map (fun c => (8405254145-1+2*2^10*c.k,114731235280730+c.lower,114731624155341+c.upper)) = pointBounds64097 := by
 decide +kernel
def cuts64098 : List PrefixCut := [⟨64,192785731,192785842⟩]
theorem checked64098 : checkPrefixCuts (2^48) 8405385217 10 Manual.Count131072.C064098.packed 64 cuts64098 = true := by
 decide +kernel
def cuts64099 : List PrefixCut := [⟨48,144897076,144897156⟩,
⟨64,193084104,193084210⟩]
theorem checked64099 : checkPrefixCuts (2^48) 8405516289 10 Manual.Count131072.C064099.packed 64 cuts64099 = true := by
 decide +kernel
def pointBounds64099 : List (Nat × Nat × Nat) := [(8405614592,114731763006295,114732151881210)]
theorem point_links_checked64099 : (cuts64099.take 1).map (fun c => (8405516289-1+2*2^10*c.k,114731618109219+c.lower,114732006984054+c.upper)) = pointBounds64099 := by
 decide +kernel
def cuts64100 : List PrefixCut := [⟨64,193449451,193449562⟩]
theorem checked64100 : checkPrefixCuts (2^48) 8405647361 10 Manual.Count131072.C064100.packed 64 cuts64100 = true := by
 decide +kernel
def cuts64101 : List PrefixCut := [⟨49,147002136,147002224⟩,
⟨64,191336832,191336944⟩]
theorem checked64101 : checkPrefixCuts (2^48) 8405778433 10 Manual.Count131072.C064101.packed 64 cuts64101 = true := by
 decide +kernel
def pointBounds64101 : List (Nat × Nat × Nat) := [(8405878784,114732151644910,114732540520050)]
theorem point_links_checked64101 : (cuts64101.take 1).map (fun c => (8405778433-1+2*2^10*c.k,114732004642774+c.lower,114732393517826+c.upper)) = pointBounds64101 := by
 decide +kernel
def cuts64102 : List PrefixCut := [⟨64,193376445,193376560⟩]
theorem checked64102 : checkPrefixCuts (2^48) 8405909505 10 Manual.Count131072.C064102.packed 64 cuts64102 = true := by
 decide +kernel
def cuts64103 : List PrefixCut := [⟨50,149307977,149308064⟩,
⟨64,192569787,192569896⟩]
theorem checked64103 : checkPrefixCuts (2^48) 8406040577 10 Manual.Count131072.C064103.packed 64 cuts64103 = true := by
 decide +kernel
def pointBounds64103 : List (Nat × Nat × Nat) := [(8406142976,114732538664028,114732927539394)]
theorem point_links_checked64103 : (cuts64103.take 1).map (fun c => (8406040577-1+2*2^10*c.k,114732389356051+c.lower,114732778231330+c.upper)) = pointBounds64103 := by
 decide +kernel
def cuts64104 : List PrefixCut := [⟨64,190423804,190423915⟩]
theorem checked64104 : checkPrefixCuts (2^48) 8406171649 10 Manual.Count131072.C064104.packed 64 cuts64104 = true := by
 decide +kernel
def cuts64105 : List PrefixCut := [⟨51,153622683,153622770⟩,
⟨64,192463339,192463448⟩]
theorem checked64105 : checkPrefixCuts (2^48) 8406302721 10 Manual.Count131072.C064105.packed 64 cuts64105 = true := by
 decide +kernel
def pointBounds64105 : List (Nat × Nat × Nat) := [(8406407168,114732925972325,114733314847911)]
theorem point_links_checked64105 : (cuts64105.take 1).map (fun c => (8406302721-1+2*2^10*c.k,114732772349642+c.lower,114733161225141+c.upper)) = pointBounds64105 := by
 decide +kernel
def cuts64106 : List PrefixCut := [⟨64,194268398,194268508⟩]
theorem checked64106 : checkPrefixCuts (2^48) 8406433793 10 Manual.Count131072.C064106.packed 64 cuts64106 = true := by
 decide +kernel
def cuts64107 : List PrefixCut := [⟨52,155057622,155057709⟩,
⟨64,190850175,190850280⟩]
theorem checked64107 : checkPrefixCuts (2^48) 8406564865 10 Manual.Count131072.C064107.packed 64 cuts64107 = true := by
 decide +kernel
def pointBounds64107 : List (Nat × Nat × Nat) := [(8406671360,114733314139001,114733703014806)]
theorem point_links_checked64107 : (cuts64107.take 1).map (fun c => (8406564865-1+2*2^10*c.k,114733159081379+c.lower,114733547957097+c.upper)) = pointBounds64107 := by
 decide +kernel
def cuts64108 : List PrefixCut := [⟨64,192119516,192119626⟩]
theorem checked64108 : checkPrefixCuts (2^48) 8406695937 10 Manual.Count131072.C064108.packed 64 cuts64108 = true := by
 decide +kernel
def cuts64109 : List PrefixCut := [⟨53,160878549,160878643⟩,
⟨64,194527183,194527294⟩]
theorem checked64109 : checkPrefixCuts (2^48) 8406827009 10 Manual.Count131072.C064109.packed 64 cuts64109 = true := by
 decide +kernel
def pointBounds64109 : List (Nat × Nat × Nat) := [(8406935552,114733702929619,114734091805646)]
theorem point_links_checked64109 : (cuts64109.take 1).map (fun c => (8406827009-1+2*2^10*c.k,114733542051070+c.lower,114733930927003+c.upper)) = pointBounds64109 := by
 decide +kernel
def cuts64110 : List PrefixCut := [⟨64,191276505,191276614⟩]
theorem checked64110 : checkPrefixCuts (2^48) 8406958081 10 Manual.Count131072.C064110.packed 64 cuts64110 = true := by
 decide +kernel
def cuts64111 : List PrefixCut := [⟨54,163049747,163049835⟩,
⟨64,191943140,191943246⟩]
theorem checked64111 : checkPrefixCuts (2^48) 8407089153 10 Manual.Count131072.C064111.packed 64 cuts64111 = true := by
 decide +kernel
def pointBounds64111 : List (Nat × Nat × Nat) := [(8407199744,114734090904505,114734479780746)]
theorem point_links_checked64111 : (cuts64111.take 1).map (fun c => (8407089153-1+2*2^10*c.k,114733927854758+c.lower,114734316730911+c.upper)) = pointBounds64111 := by
 decide +kernel
def cuts64112 : List PrefixCut := [⟨64,194685490,194685602⟩]
theorem checked64112 : checkPrefixCuts (2^48) 8407220225 10 Manual.Count131072.C064112.packed 64 cuts64112 = true := by
 decide +kernel
def cuts64113 : List PrefixCut := [⟨55,163279000,163279092⟩,
⟨64,189627077,189627183⟩]
theorem checked64113 : checkPrefixCuts (2^48) 8407351297 10 Manual.Count131072.C064113.packed 64 cuts64113 = true := by
 decide +kernel
def pointBounds64113 : List (Nat × Nat × Nat) := [(8407463936,114734477762388,114734866638851)]
theorem point_links_checked64113 : (cuts64113.take 1).map (fun c => (8407351297-1+2*2^10*c.k,114734314483388+c.lower,114734703359759+c.upper)) = pointBounds64113 := by
 decide +kernel
def cuts64114 : List PrefixCut := [⟨64,192135010,192135130⟩]
theorem checked64114 : checkPrefixCuts (2^48) 8407482369 10 Manual.Count131072.C064114.packed 64 cuts64114 = true := by
 decide +kernel
def cuts64115 : List PrefixCut := [⟨56,170438254,170438352⟩,
⟨64,193805956,193806068⟩]
theorem checked64115 : checkPrefixCuts (2^48) 8407613441 10 Manual.Count131072.C064115.packed 64 cuts64115 = true := by
 decide +kernel
def pointBounds64115 : List (Nat × Nat × Nat) := [(8407728128,114734866683729,114735255560424)]
theorem point_links_checked64115 : (cuts64115.take 1).map (fun c => (8407613441-1+2*2^10*c.k,114734696245475+c.lower,114735085122072+c.upper)) = pointBounds64115 := by
 decide +kernel
def cuts64116 : List PrefixCut := [⟨64,193903360,193903470⟩]
theorem checked64116 : checkPrefixCuts (2^48) 8407744513 10 Manual.Count131072.C064116.packed 64 cuts64116 = true := by
 decide +kernel
def cuts64117 : List PrefixCut := [⟨57,172541977,172542080⟩,
⟨64,193599033,193599147⟩]
theorem checked64117 : checkPrefixCuts (2^48) 8407875585 10 Manual.Count131072.C064117.packed 64 cuts64117 = true := by
 decide +kernel
def pointBounds64117 : List (Nat × Nat × Nat) := [(8407992320,114735256496768,114735645373690)]
theorem point_links_checked64117 : (cuts64117.take 1).map (fun c => (8407875585-1+2*2^10*c.k,114735083954791+c.lower,114735472831610+c.upper)) = pointBounds64117 := by
 decide +kernel
def cuts64118 : List PrefixCut := [⟨64,193227780,193227892⟩]
theorem checked64118 : checkPrefixCuts (2^48) 8408006657 10 Manual.Count131072.C064118.packed 64 cuts64118 = true := by
 decide +kernel
def cuts64119 : List PrefixCut := [⟨58,174143450,174143552⟩,
⟨64,192320912,192321024⟩]
theorem checked64119 : checkPrefixCuts (2^48) 8408137729 10 Manual.Count131072.C064119.packed 64 cuts64119 = true := by
 decide +kernel
def pointBounds64119 : List (Nat × Nat × Nat) := [(8408256512,114735644925054,114736033802201)]
theorem point_links_checked64119 : (cuts64119.take 1).map (fun c => (8408137729-1+2*2^10*c.k,114735470781604+c.lower,114735859658649+c.upper)) = pointBounds64119 := by
 decide +kernel
def cuts64120 : List PrefixCut := [⟨64,189740280,189740391⟩]
theorem checked64120 : checkPrefixCuts (2^48) 8408268801 10 Manual.Count131072.C064120.packed 64 cuts64120 = true := by
 decide +kernel
def cuts64121 : List PrefixCut := [⟨59,176816016,176816113⟩,
⟨64,192214488,192214594⟩]
theorem checked64121 : checkPrefixCuts (2^48) 8408399873 10 Manual.Count131072.C064121.packed 64 cuts64121 = true := by
 decide +kernel
def pointBounds64121 : List (Nat × Nat × Nat) := [(8408520704,114736029658812,114736418536177)]
theorem point_links_checked64121 : (cuts64121.take 1).map (fun c => (8408399873-1+2*2^10*c.k,114735852842796+c.lower,114736241720064+c.upper)) = pointBounds64121 := by
 decide +kernel
def cuts64122 : List PrefixCut := [⟨64,191508521,191508625⟩]
theorem checked64122 : checkPrefixCuts (2^48) 8408530945 10 Manual.Count131072.C064122.packed 64 cuts64122 = true := by
 decide +kernel
def cuts64123 : List PrefixCut := [⟨60,180660001,180660106⟩,
⟨64,192308915,192309028⟩]
theorem checked64123 : checkPrefixCuts (2^48) 8408662017 10 Manual.Count131072.C064123.packed 64 cuts64123 = true := by
 decide +kernel
def pointBounds64123 : List (Nat × Nat × Nat) := [(8408784896,114736417225806,114736806103389)]
theorem point_links_checked64123 : (cuts64123.take 1).map (fun c => (8408662017-1+2*2^10*c.k,114736236565805+c.lower,114736625443283+c.upper)) = pointBounds64123 := by
 decide +kernel
def cuts64124 : List PrefixCut := [⟨64,192071599,192071705⟩]
theorem checked64124 : checkPrefixCuts (2^48) 8408793089 10 Manual.Count131072.C064124.packed 64 cuts64124 = true := by
 decide +kernel
def cuts64125 : List PrefixCut := [⟨61,183265260,183265362⟩,
⟨64,192302928,192303035⟩]
theorem checked64125 : checkPrefixCuts (2^48) 8408924161 10 Manual.Count131072.C064125.packed 64 cuts64125 = true := by
 decide +kernel
def pointBounds64125 : List (Nat × Nat × Nat) := [(8409049088,114736804211579,114737193089378)]
theorem point_links_checked64125 : (cuts64125.take 1).map (fun c => (8408924161-1+2*2^10*c.k,114736620946319+c.lower,114737009824016+c.upper)) = pointBounds64125 := by
 decide +kernel
def cuts64126 : List PrefixCut := [⟨64,192032150,192032257⟩]
theorem checked64126 : checkPrefixCuts (2^48) 8409055233 10 Manual.Count131072.C064126.packed 64 cuts64126 = true := by
 decide +kernel
def cuts64127 : List PrefixCut := [⟨62,185100481,185100584⟩,
⟨64,191460122,191460229⟩]
theorem checked64127 : checkPrefixCuts (2^48) 8409186305 10 Manual.Count131072.C064127.packed 64 cuts64127 = true := by
 decide +kernel
def pointBounds64127 : List (Nat × Nat × Nat) := [(8409313280,114737190381878,114737579259892)]
theorem point_links_checked64127 : (cuts64127.take 1).map (fun c => (8409186305-1+2*2^10*c.k,114737005281397+c.lower,114737394159308+c.upper)) = pointBounds64127 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000128
