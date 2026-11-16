import PlattAssemblyKernel
import PlattCertificates.Count131072.C054032
import PlattCertificates.Count131072.C054033
import PlattCertificates.Count131072.C054034
import PlattCertificates.Count131072.C054035
import PlattCertificates.Count131072.C054036
import PlattCertificates.Count131072.C054037
import PlattCertificates.Count131072.C054038
import PlattCertificates.Count131072.C054039
import PlattCertificates.Count131072.C054040
import PlattCertificates.Count131072.C054041
import PlattCertificates.Count131072.C054042
import PlattCertificates.Count131072.C054043
import PlattCertificates.Count131072.C054044
import PlattCertificates.Count131072.C054045
import PlattCertificates.Count131072.C054046
import PlattCertificates.Count131072.C054047
import PlattCertificates.Count131072.C054048
import PlattCertificates.Count131072.C054049
import PlattCertificates.Count131072.C054050
import PlattCertificates.Count131072.C054051
import PlattCertificates.Count131072.C054052
import PlattCertificates.Count131072.C054053
import PlattCertificates.Count131072.C054054
import PlattCertificates.Count131072.C054055
import PlattCertificates.Count131072.C054056
import PlattCertificates.Count131072.C054057
import PlattCertificates.Count131072.C054058
import PlattCertificates.Count131072.C054059
import PlattCertificates.Count131072.C054060
import PlattCertificates.Count131072.C054061
import PlattCertificates.Count131072.C054062
import PlattCertificates.Count131072.C054063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000126
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts54032 : List PrefixCut := [⟨64,233328380,233328512⟩]
theorem checked54032 : checkPrefixCuts (2^48) 7086014465 10 Manual.Count131072.C054032.packed 64 cuts54032 = true := by
 decide +kernel
def cuts54033 : List PrefixCut := [⟨18,64746468,64746506⟩,
⟨64,227445288,227445420⟩]
theorem checked54033 : checkPrefixCuts (2^48) 7086145537 10 Manual.Count131072.C054033.packed 64 cuts54033 = true := by
 decide +kernel
def pointBounds54033 : List (Nat × Nat × Nat) := [(7086182400,112620704037490,112621091707310)]
theorem point_links_checked54033 : (cuts54033.take 1).map (fun c => (7086145537-1+2*2^10*c.k,112620639291022+c.lower,112621026960804+c.upper)) = pointBounds54033 := by
 decide +kernel
def cuts54034 : List PrefixCut := [⟨63,223826502,223826632⟩,
⟨64,228036864,228036997⟩]
theorem checked54034 : checkPrefixCuts (2^48) 7086276609 10 Manual.Count131072.C054034.packed 64 cuts54034 = true := by
 decide +kernel
def pointBounds54034 : List (Nat × Nat × Nat) := [(7086405632,112621090562812,112621478232856)]
theorem point_links_checked54034 : (cuts54034.take 1).map (fun c => (7086276609-1+2*2^10*c.k,112620866736310+c.lower,112621254406224+c.upper)) = pointBounds54034 := by
 decide +kernel
def cuts54035 : List PrefixCut := [⟨64,229144819,229144949⟩]
theorem checked54035 : checkPrefixCuts (2^48) 7086407681 10 Manual.Count131072.C054035.packed 64 cuts54035 = true := by
 decide +kernel
def cuts54036 : List PrefixCut := [⟨44,159592566,159592655⟩,
⟨64,230292457,230292586⟩]
theorem checked54036 : checkPrefixCuts (2^48) 7086538753 10 Manual.Count131072.C054036.packed 64 cuts54036 = true := by
 decide +kernel
def pointBounds54036 : List (Nat × Nat × Nat) := [(7086628864,112621483510559,112621871180825)]
theorem point_links_checked54036 : (cuts54036.take 1).map (fun c => (7086538753-1+2*2^10*c.k,112621323917993+c.lower,112621711588170+c.upper)) = pointBounds54036 := by
 decide +kernel
def cuts54037 : List PrefixCut := [⟨64,230010153,230010286⟩]
theorem checked54037 : checkPrefixCuts (2^48) 7086669825 10 Manual.Count131072.C054037.packed 64 cuts54037 = true := by
 decide +kernel
def cuts54038 : List PrefixCut := [⟨25,89564194,89564246⟩,
⟨64,230681106,230681240⟩]
theorem checked54038 : checkPrefixCuts (2^48) 7086800897 10 Manual.Count131072.C054038.packed 64 cuts54038 = true := by
 decide +kernel
def pointBounds54038 : List (Nat × Nat × Nat) := [(7086852096,112621873784797,112622261455288)]
theorem point_links_checked54038 : (cuts54038.take 1).map (fun c => (7086800897-1+2*2^10*c.k,112621784220603+c.lower,112622171891042+c.upper)) = pointBounds54038 := by
 decide +kernel
def cuts54039 : List PrefixCut := [⟨64,230517983,230518115⟩]
theorem checked54039 : checkPrefixCuts (2^48) 7086931969 10 Manual.Count131072.C054039.packed 64 cuts54039 = true := by
 decide +kernel
def cuts54040 : List PrefixCut := [⟨6,19540607,19540619⟩,
⟨64,228170412,228170543⟩]
theorem checked54040 : checkPrefixCuts (2^48) 7087063041 10 Manual.Count131072.C054040.packed 64 cuts54040 = true := by
 decide +kernel
def pointBounds54040 : List (Nat × Nat × Nat) := [(7087075328,112622264960299,112622652631016)]
theorem point_links_checked54040 : (cuts54040.take 1).map (fun c => (7087063041-1+2*2^10*c.k,112622245419692+c.lower,112622633090397+c.upper)) = pointBounds54040 := by
 decide +kernel
def cuts54041 : List PrefixCut := [⟨51,181897877,181897979⟩,
⟨64,228166233,228166361⟩]
theorem checked54041 : checkPrefixCuts (2^48) 7087194113 10 Manual.Count131072.C054041.packed 64 cuts54041 = true := by
 decide +kernel
def pointBounds54041 : List (Nat × Nat × Nat) := [(7087298560,112622655487981,112623043158919)]
theorem point_links_checked54041 : (cuts54041.take 1).map (fun c => (7087194113-1+2*2^10*c.k,112622473590104+c.lower,112622861260940+c.upper)) = pointBounds54041 := by
 decide +kernel
def cuts54042 : List PrefixCut := [⟨64,227367710,227367842⟩]
theorem checked54042 : checkPrefixCuts (2^48) 7087325185 10 Manual.Count131072.C054042.packed 64 cuts54042 = true := by
 decide +kernel
def cuts54043 : List PrefixCut := [⟨32,113066708,113066772⟩,
⟨64,227204634,227204761⟩]
theorem checked54043 : checkPrefixCuts (2^48) 7087456257 10 Manual.Count131072.C054043.packed 64 cuts54043 = true := by
 decide +kernel
def pointBounds54043 : List (Nat × Nat × Nat) := [(7087521792,112623042190755,112623429861915)]
theorem point_links_checked54043 : (cuts54043.take 1).map (fun c => (7087456257-1+2*2^10*c.k,112622929124047+c.lower,112623316795143+c.upper)) = pointBounds54043 := by
 decide +kernel
def cuts54044 : List PrefixCut := [⟨64,227875581,227875714⟩]
theorem checked54044 : checkPrefixCuts (2^48) 7087587329 10 Manual.Count131072.C054044.packed 64 cuts54044 = true := by
 decide +kernel
def cuts54045 : List PrefixCut := [⟨13,46742171,46742199⟩,
⟨64,229936414,229936546⟩]
theorem checked54045 : checkPrefixCuts (2^48) 7087718401 10 Manual.Count131072.C054045.packed 64 cuts54045 = true := by
 decide +kernel
def pointBounds54045 : List (Nat × Nat × Nat) := [(7087745024,112623430946433,112623818617817)]
theorem point_links_checked54045 : (cuts54045.take 1).map (fun c => (7087718401-1+2*2^10*c.k,112623384204262+c.lower,112623771875618+c.upper)) = pointBounds54045 := by
 decide +kernel
def cuts54046 : List PrefixCut := [⟨58,210433803,210433922⟩,
⟨64,232314902,232315032⟩]
theorem checked54046 : checkPrefixCuts (2^48) 7087849473 10 Manual.Count131072.C054046.packed 64 cuts54046 = true := by
 decide +kernel
def pointBounds54046 : List (Nat × Nat × Nat) := [(7087968256,112623824574479,112624212246086)]
theorem point_links_checked54046 : (cuts54046.take 1).map (fun c => (7087849473-1+2*2^10*c.k,112623614140676+c.lower,112624001812164+c.upper)) = pointBounds54046 := by
 decide +kernel
def cuts54047 : List PrefixCut := [⟨64,227148143,227148273⟩]
theorem checked54047 : checkPrefixCuts (2^48) 7087980545 10 Manual.Count131072.C054047.packed 64 cuts54047 = true := by
 decide +kernel
def cuts54048 : List PrefixCut := [⟨39,140615311,140615391⟩,
⟨64,230003095,230003225⟩]
theorem checked54048 : checkPrefixCuts (2^48) 7088111617 10 Manual.Count131072.C054048.packed 64 cuts54048 = true := by
 decide +kernel
def pointBounds54048 : List (Nat × Nat × Nat) := [(7088191488,112624214219032,112624601890860)]
theorem point_links_checked54048 : (cuts54048.take 1).map (fun c => (7088111617-1+2*2^10*c.k,112624073603721+c.lower,112624461275469+c.upper)) = pointBounds54048 := by
 decide +kernel
def cuts54049 : List PrefixCut := [⟨64,226146976,226147104⟩]
theorem checked54049 : checkPrefixCuts (2^48) 7088242689 10 Manual.Count131072.C054049.packed 64 cuts54049 = true := by
 decide +kernel
def cuts54050 : List PrefixCut := [⟨20,73978353,73978392⟩,
⟨64,230629941,230630068⟩]
theorem checked54050 : checkPrefixCuts (2^48) 7088373761 10 Manual.Count131072.C054050.packed 64 cuts54050 = true := by
 decide +kernel
def pointBounds54050 : List (Nat × Nat × Nat) := [(7088414720,112624603732145,112624991404190)]
theorem point_links_checked54050 : (cuts54050.take 1).map (fun c => (7088373761-1+2*2^10*c.k,112624529753792+c.lower,112624917425798+c.upper)) = pointBounds54050 := by
 decide +kernel
def cuts54051 : List PrefixCut := [⟨64,231658073,231658200⟩]
theorem checked54051 : checkPrefixCuts (2^48) 7088504833 10 Manual.Count131072.C054051.packed 64 cuts54051 = true := by
 decide +kernel
def cuts54052 : List PrefixCut := [⟨1,3573711,3573713⟩,
⟨64,228437471,228437600⟩]
theorem checked54052 : checkPrefixCuts (2^48) 7088635905 10 Manual.Count131072.C054052.packed 64 cuts54052 = true := by
 decide +kernel
def pointBounds54052 : List (Nat × Nat × Nat) := [(7088637952,112624995615517,112625383287779)]
theorem point_links_checked54052 : (cuts54052.take 1).map (fun c => (7088635905-1+2*2^10*c.k,112624992041806+c.lower,112625379714066+c.upper)) = pointBounds54052 := by
 decide +kernel
def cuts54053 : List PrefixCut := [⟨46,163393926,163394017⟩,
⟨64,228353828,228353957⟩]
theorem checked54053 : checkPrefixCuts (2^48) 7088766977 10 Manual.Count131072.C054053.packed 64 cuts54053 = true := by
 decide +kernel
def pointBounds54053 : List (Nat × Nat × Nat) := [(7088861184,112625383873203,112625771545683)]
theorem point_links_checked54053 : (cuts54053.take 1).map (fun c => (7088766977-1+2*2^10*c.k,112625220479277+c.lower,112625608151666+c.upper)) = pointBounds54053 := by
 decide +kernel
def cuts54054 : List PrefixCut := [⟨64,231684918,231685051⟩]
theorem checked54054 : checkPrefixCuts (2^48) 7088898049 10 Manual.Count131072.C054054.packed 64 cuts54054 = true := by
 decide +kernel
def cuts54055 : List PrefixCut := [⟨27,98032999,98033056⟩,
⟨64,229258624,229258756⟩]
theorem checked54055 : checkPrefixCuts (2^48) 7089029121 10 Manual.Count131072.C054055.packed 64 cuts54055 = true := by
 decide +kernel
def pointBounds54055 : List (Nat × Nat × Nat) := [(7089084416,112625778551022,112626166223730)]
theorem point_links_checked54055 : (cuts54055.take 1).map (fun c => (7089029121-1+2*2^10*c.k,112625680518023+c.lower,112626068190674+c.upper)) = pointBounds54055 := by
 decide +kernel
def cuts54056 : List PrefixCut := [⟨64,229214679,229214810⟩]
theorem checked54056 : checkPrefixCuts (2^48) 7089160193 10 Manual.Count131072.C054056.packed 64 cuts54056 = true := by
 decide +kernel
def cuts54057 : List PrefixCut := [⟨8,26323879,26323894⟩,
⟨64,231751466,231751596⟩]
theorem checked54057 : checkPrefixCuts (2^48) 7089291265 10 Manual.Count131072.C054057.packed 64 cuts54057 = true := by
 decide +kernel
def pointBounds54057 : List (Nat × Nat × Nat) := [(7089307648,112626165315205,112626552988134)]
theorem point_links_checked54057 : (cuts54057.take 1).map (fun c => (7089291265-1+2*2^10*c.k,112626138991326+c.lower,112626526664240+c.upper)) = pointBounds54057 := by
 decide +kernel
def cuts54058 : List PrefixCut := [⟨53,190694471,190694578⟩,
⟨64,229960571,229960701⟩]
theorem checked54058 : checkPrefixCuts (2^48) 7089422337 10 Manual.Count131072.C054058.packed 64 cuts54058 = true := by
 decide +kernel
def pointBounds54058 : List (Nat × Nat × Nat) := [(7089530880,112626561437263,112626949110414)]
theorem point_links_checked54058 : (cuts54058.take 1).map (fun c => (7089422337-1+2*2^10*c.k,112626370742792+c.lower,112626758415836+c.upper)) = pointBounds54058 := by
 decide +kernel
def cuts54059 : List PrefixCut := [⟨64,227494742,227494869⟩]
theorem checked54059 : checkPrefixCuts (2^48) 7089553409 10 Manual.Count131072.C054059.packed 64 cuts54059 = true := by
 decide +kernel
def cuts54060 : List PrefixCut := [⟨34,122083158,122083227⟩,
⟨64,232850266,232850398⟩]
theorem checked54060 : checkPrefixCuts (2^48) 7089684481 10 Manual.Count131072.C054060.packed 64 cuts54060 = true := by
 decide +kernel
def pointBounds54060 : List (Nat × Nat × Nat) := [(7089754112,112626950281263,112627337954633)]
theorem point_links_checked54060 : (cuts54060.take 1).map (fun c => (7089684481-1+2*2^10*c.k,112626828198105+c.lower,112627215871406+c.upper)) = pointBounds54060 := by
 decide +kernel
def cuts54061 : List PrefixCut := [⟨64,226096832,226096959⟩]
theorem checked54061 : checkPrefixCuts (2^48) 7089815553 10 Manual.Count131072.C054061.packed 64 cuts54061 = true := by
 decide +kernel
def cuts54062 : List PrefixCut := [⟨15,53555944,53555974⟩,
⟨64,230419970,230420097⟩]
theorem checked54062 : checkPrefixCuts (2^48) 7089946625 10 Manual.Count131072.C054062.packed 64 cuts54062 = true := by
 decide +kernel
def pointBounds54062 : List (Nat × Nat × Nat) := [(7089977344,112627340701147,112627728374737)]
theorem point_links_checked54062 : (cuts54062.take 1).map (fun c => (7089946625-1+2*2^10*c.k,112627287145203+c.lower,112627674818763+c.upper)) = pointBounds54062 := by
 decide +kernel
def cuts54063 : List PrefixCut := [⟨60,216004902,216005027⟩,
⟨64,230217188,230217322⟩]
theorem checked54063 : checkPrefixCuts (2^48) 7090077697 10 Manual.Count131072.C054063.packed 64 cuts54063 = true := by
 decide +kernel
def pointBounds54063 : List (Nat × Nat × Nat) := [(7090200576,112627733570075,112628121243887)]
theorem point_links_checked54063 : (cuts54063.take 1).map (fun c => (7090077697-1+2*2^10*c.k,112627517565173+c.lower,112627905238860+c.upper)) = pointBounds54063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000126
