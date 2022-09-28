function handleIt() {
                var email = document.getElementById("email");
                var username = document.getElementById("username");
                var password = document.getElementById("pwd");
                var confirm_password = document.getElementById("pwd");
                // Max length of email is 60
                var r = "";
                if (email.value == "" || username.value == "" || password.value == "" || confirm_password.value == "") {
                        r = "Please fill out all fields: \n Email \n Username \n Password \n Confirm Password \n";
                }


                if (email.value.length > 60) {
                    r += "Email length should be less than 60 characters\n";
                    
                }
                // Max length of username is 40
                if (username.value.length > 40) {
                    r += "Username length should be less than 40 characters\n";
                    
                }
                // Password exact length is 8
                if (password.value.length != 8) {
                    r += "Password length should be 8 characters\n";
                    
                }
                // Password and confirm password should be same
                if (password.value != confirm_password.value) {
                    r += "Password and confirm password should be same\n";
                    
                }
                // create alert with value r
                alert(r);
            }