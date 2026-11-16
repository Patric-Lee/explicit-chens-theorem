import PlattPointSubsetKernel
import PlattPointPackets.S6B000300
import PlattPointPackets.S6B000301
import PlattPointPackets.S6B000302
import PlattPointPackets.S6B000303
import PlattPointPackets.S6B000304
import PlattPointPackets.S6B000305
import PlattPointPackets.S6B000306
import PlattPointPackets.S6B000307
import PlattPointPackets.S6B000308
import PlattPointPackets.S6B000309
import PlattPointPackets.S6B000310
import PlattPointPackets.S6B000311
import PlattPointPackets.S6B000312
import PlattPointPackets.S7B000000
import PlattPointPackets.S7B000001
import PlattPointPackets.S7B000002
import PlattPointPackets.S7B000003
import PlattGlobalGrid.S8B000086
namespace ChenEffective.PlattWindow.PointCovers.S8B000086
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((ChenEffective.PlattWindow.PointPackets.S6B000300.points ++ ChenEffective.PlattWindow.PointPackets.S6B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000304.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S6B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000000.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000001.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000002.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000003.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000086.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000086.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000086
