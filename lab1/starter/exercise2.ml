open Core

exception Unimplemented

type weather_type = Sunny | Cloudy | Rainy of float
type forecast = {
  weather: weather_type;
  temperature: float;
  humidity: float;
}

let main () =
  let weather_to_string (w : weather_type) : string =
    match w with
    | Sunny -> "Sunny"
    | Cloudy -> "Cloudy"
    | Rainy n -> Printf.sprintf "Rainy(%.1f)" n
  in

  let forecast_to_string (f : forecast) : string =
    Printf.sprintf "{weather: %s, temp: %.1f, humidity: %.1f}"
      (weather_to_string f.weather) f.temperature f.humidity
  in

  let example_forecasts = [
    {weather = Sunny; temperature = 70.; humidity = 0.0};
    {weather = Cloudy; temperature = 62.; humidity = 0.3};
    {weather = Rainy 0.7; temperature = 55.; humidity = 0.5};
    {weather = Cloudy; temperature = 68.; humidity = 0.1};
    {weather = Rainy 0.4; temperature = 52.; humidity = 0.8};
    {weather = Rainy 0.7; temperature = 59.; humidity = 0.2};
  ] in

  let rec just_temp (l : forecast list) : float list =
    match l with 
    | [] -> []
    | x :: xs -> x.temperature :: just_temp xs
  in

  assert (just_temp example_forecasts = [70.; 62.; 55.; 68.; 52.; 59.]);

  let average_temp (l : forecast list) : float =
    let 
      sum = List.fold_left ~init:0. ~f:(+.) (just_temp l)
    in
    sum /. ( Float.of_int (List.length l))
  in

  assert (average_temp example_forecasts = 61.);

  let humid_rainy_days (l : forecast list) : forecast list =
    let is_rainy ( day: forecast ) : bool = 
      match day.weather with
      | Rainy chance -> chance >= 0.7
      | other -> false
    in
    let is_hum (day: forecast) : bool = day.humidity >= 0.5 in
    List.filter ~f:(fun x -> (is_hum x) && (is_rainy x)) l
  in

  assert (humid_rainy_days example_forecasts = [
    {weather = Rainy 0.7; temperature = 55.; humidity = 0.5}]);

  let weather_histogram (l : forecast list) : (weather_type * int) list =
    raise Unimplemented
  in

  assert (weather_histogram example_forecasts = [
    (Rainy 0.4, 1);
    (Rainy 0.7, 2);
    (Cloudy, 2);
    (Sunny, 1);
  ])

let () = main ()
