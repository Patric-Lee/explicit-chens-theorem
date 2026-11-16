import PlattAssemblyKernel
import PlattCertificates.Count131072.C030960
import PlattCertificates.Count131072.C030961
import PlattCertificates.Count131072.C030962
import PlattCertificates.Count131072.C030963
import PlattCertificates.Count131072.C030964
import PlattCertificates.Count131072.C030965
import PlattCertificates.Count131072.C030966
import PlattCertificates.Count131072.C030967
import PlattCertificates.Count131072.C030968
import PlattCertificates.Count131072.C030969
import PlattCertificates.Count131072.C030970
import PlattCertificates.Count131072.C030971
import PlattCertificates.Count131072.C030972
import PlattCertificates.Count131072.C030973
import PlattCertificates.Count131072.C030974
import PlattCertificates.Count131072.C030975
import PlattCertificates.Count131072.C030976
import PlattCertificates.Count131072.C030977
import PlattCertificates.Count131072.C030978
import PlattCertificates.Count131072.C030979
import PlattCertificates.Count131072.C030980
import PlattCertificates.Count131072.C030981
import PlattCertificates.Count131072.C030982
import PlattCertificates.Count131072.C030983
import PlattCertificates.Count131072.C030984
import PlattCertificates.Count131072.C030985
import PlattCertificates.Count131072.C030986
import PlattCertificates.Count131072.C030987
import PlattCertificates.Count131072.C030988
import PlattCertificates.Count131072.C030989
import PlattCertificates.Count131072.C030990
import PlattCertificates.Count131072.C030991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30960 : List PrefixCut := [⟨11,35756686,35756706⟩,
⟨128,410087115,410087349⟩]
theorem checked30960 : checkPrefixCuts (2^48) 4061921281 9 Manual.Count131072.C030960.packed 128 cuts30960 = true := by
 decide +kernel
def pointBounds30960 : List (Nat × Nat × Nat) := [(4061932544,105628601018396,105628984564950)]
theorem point_links_checked30960 : (cuts30960.take 1).map (fun c => (4061921281-1+2*2^9*c.k,105628565261710+c.lower,105628948808244+c.upper)) = pointBounds30960 := by
 decide +kernel
def cuts30961 : List PrefixCut := [⟨7,23837034,23837046⟩,
⟨128,409727422,409727656⟩]
theorem checked30961 : checkPrefixCuts (2^48) 4062052353 9 Manual.Count131072.C030961.packed 128 cuts30961 = true := by
 decide +kernel
def pointBounds30961 : List (Nat × Nat × Nat) := [(4062059520,105628999185859,105629382732639)]
theorem point_links_checked30961 : (cuts30961.take 1).map (fun c => (4062052353-1+2*2^9*c.k,105628975348825+c.lower,105629358895593+c.upper)) = pointBounds30961 := by
 decide +kernel
def cuts30962 : List PrefixCut := [⟨3,9770102,9770108⟩,
⟨127,406249662,406249895⟩,
⟨128,409298391,409298626⟩]
theorem checked30962 : checkPrefixCuts (2^48) 4062183425 9 Manual.Count131072.C030962.packed 128 cuts30962 = true := by
 decide +kernel
def pointBounds30962 : List (Nat × Nat × Nat) := [(4062186496,105629394846349,105629778393357),(4062313472,105629791325909,105630174873144)]
theorem point_links_checked30962 : (cuts30962.take 2).map (fun c => (4062183425-1+2*2^9*c.k,105629385076247+c.lower,105629768623249+c.upper)) = pointBounds30962 := by
 decide +kernel
def cuts30963 : List PrefixCut := [⟨123,392656348,392656570⟩,
⟨128,408592382,408592612⟩]
theorem checked30963 : checkPrefixCuts (2^48) 4062314497 9 Manual.Count131072.C030963.packed 128 cuts30963 = true := by
 decide +kernel
def pointBounds30963 : List (Nat × Nat × Nat) := [(4062440448,105630187030986,105630570578445)]
theorem point_links_checked30963 : (cuts30963.take 1).map (fun c => (4062314497-1+2*2^9*c.k,105629794374638+c.lower,105630177921875+c.upper)) = pointBounds30963 := by
 decide +kernel
def cuts30964 : List PrefixCut := [⟨119,379479552,379479773⟩,
⟨128,407678507,407678743⟩]
theorem checked30964 : checkPrefixCuts (2^48) 4062445569 9 Manual.Count131072.C030964.packed 128 cuts30964 = true := by
 decide +kernel
def pointBounds30964 : List (Nat × Nat × Nat) := [(4062567424,105630582446572,105630965994260)]
theorem point_links_checked30964 : (cuts30964.take 1).map (fun c => (4062445569-1+2*2^9*c.k,105630202967020+c.lower,105630586514487+c.upper)) = pointBounds30964 := by
 decide +kernel
def cuts30965 : List PrefixCut := [⟨115,370321976,370322187⟩,
⟨128,411060205,411060439⟩]
theorem checked30965 : checkPrefixCuts (2^48) 4062576641 9 Manual.Count131072.C030965.packed 128 cuts30965 = true := by
 decide +kernel
def pointBounds30965 : List (Nat × Nat × Nat) := [(4062694400,105630980967503,105631364515417)]
theorem point_links_checked30965 : (cuts30965.take 1).map (fun c => (4062576641-1+2*2^9*c.k,105630610645527+c.lower,105630994193230+c.upper)) = pointBounds30965 := by
 decide +kernel
def cuts30966 : List PrefixCut := [⟨111,360749371,360749575⟩,
⟨128,416658734,416658968⟩]
theorem checked30966 : checkPrefixCuts (2^48) 4062707713 9 Manual.Count131072.C030966.packed 128 cuts30966 = true := by
 decide +kernel
def pointBounds30966 : List (Nat × Nat × Nat) := [(4062821376,105631382455103,105631766003244)]
theorem point_links_checked30966 : (cuts30966.take 1).map (fun c => (4062707713-1+2*2^9*c.k,105631021705732+c.lower,105631405253669+c.upper)) = pointBounds30966 := by
 decide +kernel
def cuts30967 : List PrefixCut := [⟨107,344388017,344388207⟩,
⟨128,413874153,413874380⟩]
theorem checked30967 : checkPrefixCuts (2^48) 4062838785 9 Manual.Count131072.C030967.packed 128 cuts30967 = true := by
 decide +kernel
def pointBounds30967 : List (Nat × Nat × Nat) := [(4062948352,105631782752483,105632166300844)]
theorem point_links_checked30967 : (cuts30967.take 1).map (fun c => (4062838785-1+2*2^9*c.k,105631438364466+c.lower,105631821912637+c.upper)) = pointBounds30967 := by
 decide +kernel
def cuts30968 : List PrefixCut := [⟨103,330383050,330383233⟩,
⟨128,411643905,411644134⟩]
theorem checked30968 : checkPrefixCuts (2^48) 4062969857 9 Manual.Count131072.C030968.packed 128 cuts30968 = true := by
 decide +kernel
def pointBounds30968 : List (Nat × Nat × Nat) := [(4063075328,105632182621669,105632566170250)]
theorem point_links_checked30968 : (cuts30968.take 1).map (fun c => (4062969857-1+2*2^9*c.k,105631852238619+c.lower,105632235787017+c.upper)) = pointBounds30968 := by
 decide +kernel
def cuts30969 : List PrefixCut := [⟨99,319150011,319150187⟩,
⟨128,415510002,415510230⟩]
theorem checked30969 : checkPrefixCuts (2^48) 4063100929 9 Manual.Count131072.C030969.packed 128 cuts30969 = true := by
 decide +kernel
def pointBounds30969 : List (Nat × Nat × Nat) := [(4063202304,105632583032535,105632966581338)]
theorem point_links_checked30969 : (cuts30969.take 1).map (fun c => (4063100929-1+2*2^9*c.k,105632263882524+c.lower,105632647431151+c.upper)) = pointBounds30969 := by
 decide +kernel
def cuts30970 : List PrefixCut := [⟨95,302375830,302376002⟩,
⟨128,409400609,409400841⟩]
theorem checked30970 : checkPrefixCuts (2^48) 4063232001 9 Manual.Count131072.C030970.packed 128 cuts30970 = true := by
 decide +kernel
def pointBounds30970 : List (Nat × Nat × Nat) := [(4063329280,105632981768356,105633365317383)]
theorem point_links_checked30970 : (cuts30970.take 1).map (fun c => (4063232001-1+2*2^9*c.k,105632679392526+c.lower,105633062941381+c.upper)) = pointBounds30970 := by
 decide +kernel
def cuts30971 : List PrefixCut := [⟨92,295231335,295231503⟩,
⟨128,412296786,412297015⟩]
theorem checked30971 : checkPrefixCuts (2^48) 4063363073 9 Manual.Count131072.C030971.packed 128 cuts30971 = true := by
 decide +kernel
def pointBounds30971 : List (Nat × Nat × Nat) := [(4063457280,105633384024470,105633767573725)]
theorem point_links_checked30971 : (cuts30971.take 1).map (fun c => (4063363073-1+2*2^9*c.k,105633088793135+c.lower,105633472342222+c.upper)) = pointBounds30971 := by
 decide +kernel
def cuts30972 : List PrefixCut := [⟨89,282822874,282823039⟩,
⟨128,405287439,405287674⟩]
theorem checked30972 : checkPrefixCuts (2^48) 4063494145 9 Manual.Count131072.C030972.packed 128 cuts30972 = true := by
 decide +kernel
def pointBounds30972 : List (Nat × Nat × Nat) := [(4063585280,105633783912795,105634167462276)]
theorem point_links_checked30972 : (cuts30972.take 1).map (fun c => (4063494145-1+2*2^9*c.k,105633501089921+c.lower,105633884639237+c.upper)) = pointBounds30972 := by
 decide +kernel
def cuts30973 : List PrefixCut := [⟨86,273185852,273186009⟩,
⟨128,409776580,409776810⟩]
theorem checked30973 : checkPrefixCuts (2^48) 4063625217 9 Manual.Count131072.C030973.packed 128 cuts30973 = true := by
 decide +kernel
def pointBounds30973 : List (Nat × Nat × Nat) := [(4063713280,105634179563212,105634563112920)]
theorem point_links_checked30973 : (cuts30973.take 1).map (fun c => (4063625217-1+2*2^9*c.k,105633906377360+c.lower,105634289926911+c.upper)) = pointBounds30973 := by
 decide +kernel
def cuts30974 : List PrefixCut := [⟨83,264657685,264657839⟩,
⟨128,409486335,409486572⟩]
theorem checked30974 : checkPrefixCuts (2^48) 4063756289 9 Manual.Count131072.C030974.packed 128 cuts30974 = true := by
 decide +kernel
def pointBounds30974 : List (Nat × Nat × Nat) := [(4063841280,105634580811625,105634964361560)]
theorem point_links_checked30974 : (cuts30974.take 1).map (fun c => (4063756289-1+2*2^9*c.k,105634316153940+c.lower,105634699703721+c.upper)) = pointBounds30974 := by
 decide +kernel
def cuts30975 : List PrefixCut := [⟨80,257792322,257792470⟩,
⟨128,411412461,411412694⟩]
theorem checked30975 : checkPrefixCuts (2^48) 4063887361 9 Manual.Count131072.C030975.packed 128 cuts30975 = true := by
 decide +kernel
def pointBounds30975 : List (Nat × Nat × Nat) := [(4063969280,105634983432597,105635366982763)]
theorem point_links_checked30975 : (cuts30975.take 1).map (fun c => (4063887361-1+2*2^9*c.k,105634725640275+c.lower,105635109190293+c.upper)) = pointBounds30975 := by
 decide +kernel
def cuts30976 : List PrefixCut := [⟨77,252866675,252866811⟩,
⟨128,412645915,412646144⟩]
theorem checked30976 : checkPrefixCuts (2^48) 4064018433 9 Manual.Count131072.C030976.packed 128 cuts30976 = true := by
 decide +kernel
def pointBounds30976 : List (Nat × Nat × Nat) := [(4064097280,105635389919411,105635773469798)]
theorem point_links_checked30976 : (cuts30976.take 1).map (fun c => (4064018433-1+2*2^9*c.k,105635137052736+c.lower,105635520602987+c.upper)) = pointBounds30976 := by
 decide +kernel
def cuts30977 : List PrefixCut := [⟨74,239769016,239769152⟩,
⟨128,413048150,413048386⟩]
theorem checked30977 : checkPrefixCuts (2^48) 4064149505 9 Manual.Count131072.C030977.packed 128 cuts30977 = true := by
 decide +kernel
def pointBounds30977 : List (Nat × Nat × Nat) := [(4064225280,105635789467667,105636173018283)]
theorem point_links_checked30977 : (cuts30977.take 1).map (fun c => (4064149505-1+2*2^9*c.k,105635549698651+c.lower,105635933249131+c.upper)) = pointBounds30977 := by
 decide +kernel
def cuts30978 : List PrefixCut := [⟨71,226256587,226256715⟩,
⟨128,408325447,408325684⟩]
theorem checked30978 : checkPrefixCuts (2^48) 4064280577 9 Manual.Count131072.C030978.packed 128 cuts30978 = true := by
 decide +kernel
def pointBounds30978 : List (Nat × Nat × Nat) := [(4064353280,105636189003388,105636572554232)]
theorem point_links_checked30978 : (cuts30978.take 1).map (fun c => (4064280577-1+2*2^9*c.k,105635962746801+c.lower,105636346297517+c.upper)) = pointBounds30978 := by
 decide +kernel
def cuts30979 : List PrefixCut := [⟨68,215099636,215099763⟩,
⟨128,409766518,409766752⟩]
theorem checked30979 : checkPrefixCuts (2^48) 4064411649 9 Manual.Count131072.C030979.packed 128 cuts30979 = true := by
 decide +kernel
def pointBounds30979 : List (Nat × Nat × Nat) := [(4064481280,105636586171884,105636969722964)]
theorem point_links_checked30979 : (cuts30979.take 1).map (fun c => (4064411649-1+2*2^9*c.k,105636371072248+c.lower,105636754623201+c.upper)) = pointBounds30979 := by
 decide +kernel
def cuts30980 : List PrefixCut := [⟨65,209968246,209968363⟩,
⟨128,411207630,411207864⟩]
theorem checked30980 : checkPrefixCuts (2^48) 4064542721 9 Manual.Count131072.C030980.packed 128 cuts30980 = true := by
 decide +kernel
def pointBounds30980 : List (Nat × Nat × Nat) := [(4064609280,105636990807012,105637374358316)]
theorem point_links_checked30980 : (cuts30980.take 1).map (fun c => (4064542721-1+2*2^9*c.k,105636780838766+c.lower,105637164389953+c.upper)) = pointBounds30980 := by
 decide +kernel
def cuts30981 : List PrefixCut := [⟨62,194588374,194588478⟩,
⟨128,404754277,404754504⟩]
theorem checked30981 : checkPrefixCuts (2^48) 4064673793 9 Manual.Count131072.C030981.packed 128 cuts30981 = true := by
 decide +kernel
def pointBounds30981 : List (Nat × Nat × Nat) := [(4064737280,105637386634770,105637770186295)]
theorem point_links_checked30981 : (cuts30981.take 1).map (fun c => (4064673793-1+2*2^9*c.k,105637192046396+c.lower,105637575597817+c.upper)) = pointBounds30981 := by
 decide +kernel
def cuts30982 : List PrefixCut := [⟨59,190150428,190150533⟩,
⟨128,412496814,412497038⟩]
theorem checked30982 : checkPrefixCuts (2^48) 4064804865 9 Manual.Count131072.C030982.packed 128 cuts30982 = true := by
 decide +kernel
def pointBounds30982 : List (Nat × Nat × Nat) := [(4064865280,105637786951101,105638170502854)]
theorem point_links_checked30982 : (cuts30982.take 1).map (fun c => (4064804865-1+2*2^9*c.k,105637596800673+c.lower,105637980352321+c.upper)) = pointBounds30982 := by
 decide +kernel
def cuts30983 : List PrefixCut := [⟨56,176295527,176295626⟩,
⟨128,407982623,407982851⟩]
theorem checked30983 : checkPrefixCuts (2^48) 4064935937 9 Manual.Count131072.C030983.packed 128 cuts30983 = true := by
 decide +kernel
def pointBounds30983 : List (Nat × Nat × Nat) := [(4064993280,105638185593014,105638569144985)]
theorem point_links_checked30983 : (cuts30983.take 1).map (fun c => (4064935937-1+2*2^9*c.k,105638009297487+c.lower,105638392849359+c.upper)) = pointBounds30983 := by
 decide +kernel
def cuts30984 : List PrefixCut := [⟨53,169434957,169435052⟩,
⟨128,409839018,409839253⟩]
theorem checked30984 : checkPrefixCuts (2^48) 4065067009 9 Manual.Count131072.C030984.packed 128 cuts30984 = true := by
 decide +kernel
def pointBounds30984 : List (Nat × Nat × Nat) := [(4065121280,105638586715067,105638970267262)]
theorem point_links_checked30984 : (cuts30984.take 1).map (fun c => (4065067009-1+2*2^9*c.k,105638417280110+c.lower,105638800832210+c.upper)) = pointBounds30984 := by
 decide +kernel
def cuts30985 : List PrefixCut := [⟨50,161536234,161536324⟩,
⟨128,414672522,414672758⟩]
theorem checked30985 : checkPrefixCuts (2^48) 4065198081 9 Manual.Count131072.C030985.packed 128 cuts30985 = true := by
 decide +kernel
def pointBounds30985 : List (Nat × Nat × Nat) := [(4065249280,105638988655362,105639372207787)]
theorem point_links_checked30985 : (cuts30985.take 1).map (fun c => (4065198081-1+2*2^9*c.k,105638827119128+c.lower,105639210671463+c.upper)) = pointBounds30985 := by
 decide +kernel
def cuts30986 : List PrefixCut := [⟨47,148445209,148445296⟩,
⟨128,405519886,405520119⟩]
theorem checked30986 : checkPrefixCuts (2^48) 4065329153 9 Manual.Count131072.C030986.packed 128 cuts30986 = true := by
 decide +kernel
def pointBounds30986 : List (Nat × Nat × Nat) := [(4065377280,105639390236859,105639773789517)]
theorem point_links_checked30986 : (cuts30986.take 1).map (fun c => (4065329153-1+2*2^9*c.k,105639241791650+c.lower,105639625344221+c.upper)) = pointBounds30986 := by
 decide +kernel
def cuts30987 : List PrefixCut := [⟨44,140824588,140824670⟩,
⟨128,411945615,411945849⟩]
theorem checked30987 : checkPrefixCuts (2^48) 4065460225 9 Manual.Count131072.C030987.packed 128 cuts30987 = true := by
 decide +kernel
def pointBounds30987 : List (Nat × Nat × Nat) := [(4065505280,105639788136124,105640171689010)]
theorem point_links_checked30987 : (cuts30987.take 1).map (fun c => (4065460225-1+2*2^9*c.k,105639647311536+c.lower,105640030864340+c.upper)) = pointBounds30987 := by
 decide +kernel
def cuts30988 : List PrefixCut := [⟨41,133758323,133758401⟩,
⟨128,411516984,411517219⟩]
theorem checked30988 : checkPrefixCuts (2^48) 4065591297 9 Manual.Count131072.C030988.packed 128 cuts30988 = true := by
 decide +kernel
def pointBounds30988 : List (Nat × Nat × Nat) := [(4065633280,105640193015474,105640576568590)]
theorem point_links_checked30988 : (cuts30988.take 1).map (fun c => (4065591297-1+2*2^9*c.k,105640059257151+c.lower,105640442810189+c.upper)) = pointBounds30988 := by
 decide +kernel
def cuts30989 : List PrefixCut := [⟨38,125307905,125307975⟩,
⟨128,411365292,411365522⟩]
theorem checked30989 : checkPrefixCuts (2^48) 4065722369 9 Manual.Count131072.C030989.packed 128 cuts30989 = true := by
 decide +kernel
def pointBounds30989 : List (Nat × Nat × Nat) := [(4065761280,105640596082040,105640979635383)]
theorem point_links_checked30989 : (cuts30989.take 1).map (fun c => (4065722369-1+2*2^9*c.k,105640470774135+c.lower,105640854327408+c.upper)) = pointBounds30989 := by
 decide +kernel
def cuts30990 : List PrefixCut := [⟨35,110627418,110627486⟩,
⟨128,408513618,408513857⟩]
theorem checked30990 : checkPrefixCuts (2^48) 4065853441 9 Manual.Count131072.C030990.packed 128 cuts30990 = true := by
 decide +kernel
def pointBounds30990 : List (Nat × Nat × Nat) := [(4065889280,105640992766845,105641376320416)]
theorem point_links_checked30990 : (cuts30990.take 1).map (fun c => (4065853441-1+2*2^9*c.k,105640882139427+c.lower,105641265692930+c.upper)) = pointBounds30990 := by
 decide +kernel
def cuts30991 : List PrefixCut := [⟨32,102593629,102593688⟩,
⟨128,407946681,407946906⟩]
theorem checked30991 : checkPrefixCuts (2^48) 4065984513 9 Manual.Count131072.C030991.packed 128 cuts30991 = true := by
 decide +kernel
def pointBounds30991 : List (Nat × Nat × Nat) := [(4066017280,105641393246674,105641776800475)]
theorem point_links_checked30991 : (cuts30991.take 1).map (fun c => (4065984513-1+2*2^9*c.k,105641290653045+c.lower,105641674206787+c.upper)) = pointBounds30991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000030
