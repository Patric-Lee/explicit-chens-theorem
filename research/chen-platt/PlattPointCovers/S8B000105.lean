import PlattPointSubsetKernel
import PlattPointPackets.S7B000295
import PlattPointPackets.S7B000296
import PlattPointPackets.S7B000297
import PlattPointPackets.S7B000298
import PlattPointPackets.S7B000299
import PlattPointPackets.S7B000300
import PlattPointPackets.S7B000301
import PlattPointPackets.S7B000302
import PlattPointPackets.S7B000303
import PlattPointPackets.S7B000304
import PlattPointPackets.S7B000305
import PlattPointPackets.S7B000306
import PlattPointPackets.S7B000307
import PlattPointPackets.S7B000308
import PlattPointPackets.S7B000309
import PlattPointPackets.S7B000310
import PlattPointPackets.S7B000311
import PlattPointPackets.S7B000312
import PlattPointPackets.S8B000000
import PlattGlobalGrid.S8B000105
namespace ChenEffective.PlattWindow.PointCovers.S8B000105
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((((((((((ChenEffective.PlattWindow.PointPackets.S7B000295.points ++ ChenEffective.PlattWindow.PointPackets.S7B000296.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000297.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000298.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000299.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000300.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000304.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000309.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000310.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000311.points) ++ ChenEffective.PlattWindow.PointPackets.S7B000312.points) ++ ChenEffective.PlattWindow.PointPackets.S8B000000.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000105.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000105.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000105
