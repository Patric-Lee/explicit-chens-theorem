import PlattPointSubsetKernel
import PlattPointPackets.S4B000298
import PlattPointPackets.S4B000299
import PlattPointPackets.S4B000300
import PlattPointPackets.S4B000301
import PlattPointPackets.S4B000302
import PlattPointPackets.S4B000303
import PlattPointPackets.S4B000304
import PlattPointPackets.S4B000305
import PlattPointPackets.S4B000306
import PlattPointPackets.S4B000307
import PlattPointPackets.S4B000308
import PlattGlobalGrid.S8B000035
namespace ChenEffective.PlattWindow.PointCovers.S8B000035
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((((((((ChenEffective.PlattWindow.PointPackets.S4B000298.points ++ ChenEffective.PlattWindow.PointPackets.S4B000299.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000300.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000301.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000302.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000303.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000304.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S4B000308.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S8B000035.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S8B000035.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S8B000035
